{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Evaluation.StructuralLists (test_structuralLists) where

import PlutusPrelude

import Evaluation.Builtins.Common (typecheckAnd)
import PlutusCore qualified as PLC
import PlutusCore.Builtin
import PlutusCore.Compiler.Erase (eraseTerm)
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.Ck qualified as CK
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.ExMemoryUsage (memoryUsage)
import PlutusCore.Flat (flat, unflat)
import PlutusCore.MkPlc (mkConstant, mkIterAppNoAnn)
import PlutusCore.Pretty (displayPlc)
import PlutusCore.SnocList qualified as SnocList
import PlutusCore.TypeCheck (TypeErrorPlc)
import PlutusCore.Version
import UntypedPlutusCore (UnrestrictedProgram (..))
import UntypedPlutusCore qualified as U
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as CEK
import UntypedPlutusCore.Evaluation.Machine.SteppableCek qualified as SCEK
import UntypedPlutusCore.Parser qualified as Parser

import Control.Monad.Except (runExcept)
import Data.Text (Text)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck qualified as QC

type Term = U.Term PLC.Name DefaultUni DefaultFun ()
type TypedTerm = PLC.Term PLC.TyName PLC.Name DefaultUni DefaultFun ()

appendTerms :: Term -> Term -> Term
appendTerms xs ys = mkIterAppNoAnn (U.Force () $ U.Builtin () TermAppend) [xs, ys]

integer :: Integer -> Term
integer = mkConstant ()

integers :: [Integer] -> Term
integers = mkConstant ()

traceTerm :: Text -> Term -> Term
traceTerm msg x = mkIterAppNoAnn (U.Force () $ U.Builtin () Trace) [mkConstant () msg, x]

typedAppend :: TypedTerm
typedAppend =
  mkIterAppNoAnn
    (PLC.TyInst () (PLC.Builtin () TermAppend) $ mkTyBuiltin @_ @Integer ())
    [ PLC.List
        ()
        (mkTyBuiltin @_ @Integer ())
        [mkConstant () (1 :: Integer), mkConstant () (2 :: Integer)]
    , mkConstant () ([3] :: [Integer])
    ]

wellTyped :: TypedTerm -> Bool
wellTyped t =
  isRight
    ( typecheckAnd def (\_ _ -> ()) defaultBuiltinCostModelForTesting t
        :: Either (TypeErrorPlc DefaultUni DefaultFun ()) ()
    )

optimize :: Term -> Term
optimize = fst . PLC.runQuote . U.runOptimizerT . U.termOptimizer U.defaultOptimizeOpts def

test_structuralLists :: TestTree
test_structuralLists =
  testGroup "structural lists" $
    [ testGroup name (runtimeTests eval)
    | (name, eval) <-
        [ ("CEK", CEK.evaluateCek CEK.logEmitter defaultCekParametersForTesting)
        , ("SteppableCEK", SCEK.evaluateCek SCEK.logEmitter defaultCekParametersForTesting)
        ,
          ( "optimized CEK"
          , CEK.evaluateCek CEK.logEmitter defaultCekParametersForTesting . optimize
          )
        ]
    ]
      ++ [ testGroup
             "integration"
             [ testCase "typed conversion and CK/CEK agreement" $ do
                 assertBool "well typed" $ wellTyped typedAppend
                 let result =
                       CK.evaluateCkNoEmit
                         (toBuiltinsRuntime def defaultBuiltinCostModelForTesting)
                         def
                         typedAppend
                 fmap eraseTerm result @?= Right (integers [1, 2, 3])
             , testCase "empty structural list at an abstract type" $ do
                 let t = PLC.runQuote $ do
                       a <- PLC.freshTyName "a"
                       pure $ PLC.TyAbs () a (PLC.Type ()) (PLC.List () (PLC.TyVar () a) [])
                 assertBool "well typed" $ wellTyped t
             , testCase "function elements are well typed" $ do
                 let t = PLC.runQuote $ do
                       x <- PLC.freshName "x"
                       let intTy = mkTyBuiltin @_ @Integer ()
                       pure $
                         PLC.List
                           ()
                           (PLC.TyFun () intTy intTy)
                           [PLC.LamAbs () x intTy (PLC.Var () x)]
                 assertBool "well typed" $ wellTyped t
             , testCase "heterogeneous structural list is ill typed" $
                 assertBool "ill typed" $
                   not $
                     wellTyped $
                       PLC.List () (mkTyBuiltin @_ @Integer ()) [mkConstant () True]
             , testCase "prefix and tail element types must agree" $
                 assertBool "ill typed" $
                   not $
                     wellTyped $
                       mkIterAppNoAnn
                         (PLC.TyInst () (PLC.Builtin () TermAppend) $ mkTyBuiltin @_ @Integer ())
                         [ PLC.List () (mkTyBuiltin @_ @Bool ()) [mkConstant () True]
                         , mkConstant () ([] :: [Integer])
                         ]
             , testCase "cost does not depend on the tail length" $ do
                 let cost ys =
                       snd $
                         CEK.runCekNoEmit defaultCekParametersForTesting CEK.counting $
                           appendTerms (U.List () [integer 1]) (integers ys)
                 cost [] @?= cost [1 .. 10000]
             , testCase "snoc-list costing preserves list cost chunks" $
                 for_ [0, 1, 99, 100, 101, 199, 200, 201, 1000 :: Int] $ \n -> do
                   let xs = [1 .. n]
                   show (memoryUsage (SnocList.fromList xs)) @?= show (memoryUsage xs)
             , testCase "typed Flat round trip" $
                 unflat (flat typedAppend) @?= Right typedAppend
             , testCase "UPLC Flat round trip" $ do
                 let p =
                       U.Program () plcVersion130 $
                         appendTerms (U.List () [integer 1]) (integers [])
                 fmap unUnrestrictedProgram (unflat $ flat $ UnrestrictedProgram p) @?= Right p
             , testCase "UPLC Flat rejects List before 1.3.0" $ do
                 let p = UnrestrictedProgram $ U.Program () plcVersion120 (U.List () [] :: Term)
                 case unflat (flat p) of
                   Left _ -> pure ()
                   Right actual ->
                     assertFailure $
                       "Unexpected round trip: "
                         ++ show (unUnrestrictedProgram actual == unUnrestrictedProgram p)
             , testCase "text round trip" $ do
                 let p =
                       U.Program () plcVersion130 $
                         appendTerms (U.List () [integer 1]) (integers [])
                 fmap void (runExcept $ PLC.runQuoteT $ Parser.parseProgram $ displayPlc p)
                   @?= Right p
             , testCase "text rejects List before 1.3.0" $
                 assertBool "rejected" $
                   isLeft $
                     runExcept $
                       PLC.runQuoteT (Parser.parseProgram "(program 1.2.0 (list))")
             ]
         ]
  where
    runtimeTests eval =
      [ QC.testProperty "agrees with (++)" $ \xs ys ->
          fst (eval $ appendTerms (U.List () $ map integer xs) (integers ys))
            == Right (integers (xs ++ ys))
      , testCase "empty prefix returns tail" $
          fst (eval $ appendTerms (U.List () []) (integers [1, 2])) @?= Right (integers [1, 2])
      , testCase "computed elements" $
          let sumTerm = mkIterAppNoAnn (U.Builtin () AddInteger) [integer 1, integer 2]
           in fst (eval $ appendTerms (U.List () [sumTerm]) (integers []))
                @?= Right (integers [3])
      , testCase "discharging nested structural lists preserves source order" $ do
          let term =
                U.List
                  ()
                  [U.List () [integer 1, integer 2], U.List () [integer 3, integer 4]]
          fst (eval term) @?= Right term
      , testCase "left-to-right effects, then tail" $ do
          let term =
                appendTerms
                  (U.List () [traceTerm "first" (integer 1), traceTerm "second" (integer 2)])
                  (traceTerm "tail" $ integers [3])
          eval term @?= (Right (integers [1, 2, 3]), ["first", "second", "tail"])
      , testCase "element failure stops evaluation" $ do
          let term =
                appendTerms
                  ( U.List
                      ()
                      [ U.Force () $ traceTerm "first" (U.Delay () $ U.Error ())
                      , traceTerm "second" (integer 2)
                      ]
                  )
                  (traceTerm "tail" $ integers [])
              (result, logs) = eval term
          assertBool "failed" $ isLeft result
          logs @?= ["first"]
      , testCase "type mismatch is detected after evaluating the tail" $ do
          let (result, logs) =
                eval $
                  appendTerms
                    (U.List () [mkConstant () True])
                    (traceTerm "tail" $ integers [])
          assertBool "failed" $ isLeft result
          logs @?= ["tail"]
      , testCase "builtin list cannot substitute for structural prefix" $
          assertBool "failed" $
            isLeft $
              fst $
                eval $
                  appendTerms (integers [1]) (integers [])
      , testCase "tail must be a builtin list, including for empty prefix" $
          assertBool "failed" $
            isLeft $
              fst $
                eval $
                  appendTerms (U.List () []) (integer 1)
      , testCase "structural lists can contain closures" $ do
          let x = PLC.Name "x" (PLC.Unique 0)
              closure = U.LamAbs () x (U.Var () x)
          fst (eval $ U.List () [closure]) @?= Right (U.List () [closure])
          assertBool "conversion rejects closure" $
            isLeft $
              fst $
                eval $
                  appendTerms (U.List () [closure]) (integers [])
      , testCase "list returned through a function" $ do
          let x = PLC.Name "x" (PLC.Unique 0)
              prefix = U.Apply () (U.LamAbs () x $ U.List () [U.Var () x]) (integer 4)
          fst (eval $ appendTerms prefix (integers [5])) @?= Right (integers [4, 5])
      , testCase "nested builtin elements" $ do
          let term =
                appendTerms
                  (U.List () [integers [1, 2]])
                  (mkConstant () ([[3]] :: [[Integer]]))
          fst (eval term) @?= Right (mkConstant () ([[1, 2], [3]] :: [[Integer]]))
      , testCase "large prefix" $
          let xs = [1 .. 10000]
           in fst (eval $ appendTerms (U.List () $ map integer xs) (integers []))
                @?= Right (integers xs)
      ]
