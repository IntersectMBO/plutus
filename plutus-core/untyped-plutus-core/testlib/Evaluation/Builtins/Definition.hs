-- editorconfig-checker-disable-file
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- Sure GHC, I'm enabling the extension just so that you can warn me about its usages.
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

-- | Tests for all kinds of built-in functions.
module Evaluation.Builtins.Definition
  ( test_definition
  ) where

import PlutusPrelude

import Evaluation.Builtins.BLS12_381 (test_BLS12_381)
import Evaluation.Builtins.Bitwise.CIP0122 qualified as CIP0122
import Evaluation.Builtins.Bitwise.CIP0123 qualified as CIP0123
import Evaluation.Builtins.Common
  ( typecheckAnd
  , typecheckEvaluateCek
  , typecheckEvaluateCekNoEmit
  , typecheckReadKnownCek
  )
import Evaluation.Builtins.Conversion qualified as Conversion
import Evaluation.Builtins.Integer.DivModProperties (test_integer_div_mod_properties)
import Evaluation.Builtins.Integer.ExpModIntegerProperties (test_integer_exp_mod_properties)
import Evaluation.Builtins.Integer.OrderProperties (test_integer_order_properties)
import Evaluation.Builtins.Integer.QuotRemProperties (test_integer_quot_rem_properties)
import Evaluation.Builtins.Integer.RingProperties (test_integer_ring_properties)
import Evaluation.Builtins.SignatureVerification
  ( ecdsaSecp256k1Prop
  , ed25519_VariantAProp
  , ed25519_VariantBProp
  , ed25519_VariantCProp
  , schnorrSecp256k1Prop
  )

import PlutusCore hiding (Constr)
import PlutusCore qualified as PLC
import PlutusCore.Builtin
import PlutusCore.Compiler.Erase (eraseTerm)
import PlutusCore.Data
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Examples.Builtins
import PlutusCore.Examples.Data.Data
import PlutusCore.Generators.Hedgehog.Interesting
import PlutusCore.Generators.QuickCheck.Builtin
import PlutusCore.MkPlc hiding (error)
import PlutusCore.Pretty
import PlutusCore.StdLib.Data.Bool
import PlutusCore.StdLib.Data.Data
import PlutusCore.StdLib.Data.Function qualified as Plc
import PlutusCore.StdLib.Data.Integer
import PlutusCore.StdLib.Data.List qualified as Builtin
import PlutusCore.StdLib.Data.MatchOption
import PlutusCore.StdLib.Data.Pair
import PlutusCore.StdLib.Data.ScottList qualified as Scott
import PlutusCore.StdLib.Data.ScottUnit qualified as Scott
import PlutusCore.StdLib.Data.Unit
import PlutusCore.Test
import UntypedPlutusCore.Evaluation.Machine.Cek

import Control.Exception (evaluate, try)
import Data.Bifunctor (bimap)
import Data.ByteString (ByteString, pack)
import Data.ByteString.Base16 qualified as Base16
import Data.DList qualified as DList
import Data.List (find)
import Data.Proxy (Proxy (..))
import Data.String (IsString (fromString))
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Vector.Strict (Vector)
import Data.Vector.Strict qualified as Vector
import Hedgehog (forAll, property, withTests, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Prettyprinter (vsep)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@=?), (@?=))
import Test.Tasty.Hedgehog (testPropertyNamed)
import Test.Tasty.QuickCheck qualified as QC

type DefaultFunExt = Either DefaultFun ExtensionFun

runTestNestedHere :: [TestNested] -> TestTree
runTestNestedHere =
  runTestNested
    ["untyped-plutus-core", "test", "Evaluation", "Builtins", "Golden"]

defaultBuiltinCostModelExt :: CostingPart DefaultUni DefaultFunExt
defaultBuiltinCostModelExt = (defaultBuiltinCostModelForTesting, ())

{- FIXME: in this module there are many occurrences of things like

     typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting

   Here `def` is the default semantics variant defined in
   PlutusCore.Default.Builtins.  Currently that is equal to
   `DefaultFunSemanticsVariantC`, and `defaultBuiltinCostModelForTesting` is the
   cost model for the same variant.  Can we couple these things together more
   tightly so that it's guaranteed that the two things refer to the same
   semantics variant?
-}

test_IntegerDistribution :: TestTree
test_IntegerDistribution =
  QC.testProperty "distribution of 'Integer' constants" . QC.withMaxSuccess 10000 $
    \(AsArbitraryBuiltin (i :: Integer)) ->
      let magnitudes = magnitudesPositive nextInterestingBound highInterestingBound
          (low, high) =
            maybe (error "Panic: unknown integer") (bimap (* signum i) (* signum i)) $
              find ((>= abs i) . snd) magnitudes
          bounds = map snd magnitudes
          isInteresting =
            i
              `elem` concat
                [ map (pred . negate) bounds
                , map negate bounds
                , [-1, 0, 1]
                , bounds
                , map succ bounds
                ]
       in ( if i /= 0
              then QC.label $ "(" ++ show low ++ ", " ++ show high ++ ")"
              else QC.property
          )
            ( ( if isInteresting
                  then QC.label $ show i
                  else QC.property
              )
                True
            )

{-| Check that the 'Factorial' builtin computes to the same thing as factorial defined in PLC
itself. -}
test_Factorial :: TestTree
test_Factorial =
  testCase "Factorial" $ do
    let ten = mkConstant @Integer @DefaultUni () 10
        lhs =
          typecheckEvaluateCek def defaultBuiltinCostModelExt $
            apply () (builtin () $ Right Factorial) ten
        rhs =
          typecheckEvaluateCek def defaultBuiltinCostModelExt $
            apply () (mapFun Left factorial) ten
    assertBool "type checks" $ isRight lhs
    lhs @?= rhs

{-| Check that 'Const' from the above computes to the same thing as
a const defined in PLC itself. -}
test_Const :: TestTree
test_Const =
  testPropertyNamed "Const" "Const" . withTests 10 . property $ do
    c <- forAll $ Gen.text (Range.linear 0 100) Gen.unicode
    b <- forAll Gen.bool
    let tC = mkConstant () c
        tB = mkConstant () b
        text = toTypeAst @_ @_ @DefaultUni @Text Proxy
        runConst con = mkIterAppNoAnn (mkIterInstNoAnn con [text, bool]) [tC, tB]
        lhs =
          typecheckReadKnownCek def defaultBuiltinCostModelExt $
            runConst $
              builtin () (Right Const)
        rhs =
          typecheckReadKnownCek def defaultBuiltinCostModelExt $
            runConst $
              mapFun @DefaultFun Left Plc.const
    lhs === Right (Right c)
    lhs === rhs

{-| Test that forcing a builtin accepting one type argument and no term arguments makes the
builtin compute properly. -}
test_ForallFortyTwo :: TestTree
test_ForallFortyTwo =
  testCase "ForallFortyTwo" $ do
    let term = tyInst () (builtin () ForallFortyTwo) $ mkTyBuiltin @_ @() ()
        lhs = typecheckEvaluateCekNoEmit def () term
        rhs = Right $ EvaluationSuccess $ mkConstant @Integer () 42
    lhs @?= rhs

{-| Test that a polymorphic built-in function doesn't subvert the CEK machine.
See https://github.com/IntersectMBO/plutus/issues/1882 -}
test_Id :: TestTree
test_Id =
  testCase "Id" $ do
    let zer = mkConstant @Integer @DefaultUni @DefaultFunExt () 0
        oneT = mkConstant @Integer @DefaultUni () 1
        oneU = mkConstant @Integer @DefaultUni () 1
        -- > id {integer -> integer} ((\(i : integer) (j : integer) -> i) 1) 0
        term =
          mkIterAppNoAnn
            (tyInst () (builtin () $ Right Id) (TyFun () integer integer))
            [ apply () constIntegerInteger oneT
            , zer
            ]
          where
            constIntegerInteger = runQuote $ do
              i <- freshName "i"
              j <- freshName "j"
              return
                . LamAbs () i integer
                . LamAbs () j integer
                $ Var () i
    typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term
      @?= Right (EvaluationSuccess oneU)

{-| Test that a polymorphic built-in function can have a higher-kinded type variable in its
signature. -}
test_IdFInteger :: TestTree
test_IdFInteger =
  testCase "IdFInteger" $ do
    let one = mkConstant @Integer @DefaultUni () 1
        ten = mkConstant @Integer @DefaultUni () 10
        res = mkConstant @Integer @DefaultUni () 55
        -- > sum (idFInteger {list} (enumFromTo 1 10))
        term =
          apply () (mapFun Left Scott.sum)
            . apply () (tyInst () (builtin () $ Right IdFInteger) Scott.listTy)
            $ mkIterAppNoAnn (mapFun Left Scott.enumFromTo) [one, ten]
    typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term
      @?= Right (EvaluationSuccess res)

test_IdList :: TestTree
test_IdList =
  testCase "IdList" $ do
    let tyAct = typeOfBuiltinFunction @DefaultUni def IdList
        tyExp =
          let a = TyName . Name "a" $ Unique 0
              listA = TyApp () Scott.listTy (TyVar () a)
           in TyForall () a (Type ()) $ TyFun () listA listA
        one = mkConstant @Integer @DefaultUni () 1
        ten = mkConstant @Integer @DefaultUni () 10
        res = mkConstant @Integer @DefaultUni () 55
        -- > sum (idList {integer} (enumFromTo 1 10))
        term =
          apply () (mapFun Left Scott.sum)
            . apply () (tyInst () (builtin () $ Right IdList) integer)
            $ mkIterAppNoAnn (mapFun Left Scott.enumFromTo) [one, ten]
    tyAct @?= tyExp
    typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term
      @?= Right (EvaluationSuccess res)

{- Note [Higher-rank built-in functions]
We can't unlift a monomorphic function passed to a built-in function, let alone unlift a polymorphic
one, however we can define a built-in function that accepts an 'Opaque' term of a polymorphic type.
However, as is always the case with an 'Opaque' term, we can't inspect it or use it in any
non-opaque way, so a function of type

    all (f :: * -> *). (all (a :: *). f a) -> all (a :: *). f a

can be assigned the following meaning on the Haskell side:

    \x -> x

but we have no way of providing a meaning for a built-in function with the following signature:

    all (f :: * -> *). all (a :: *). (all (a :: *). f a) -> f a

That's because the meaning function would have to instantiate the @all (a :: *). f a@ argument
somehow to get an @f a@, but that is exactly "using a term in a non-opaque way".

Basically, since we are either generic over @term@ or, like in the example below, use 'CekValue',
there's is no sensible way of instantiating a passed polymorphic argument (or applying a passed
argument when it's a function, for another example).
-}

-- | Test that opaque terms with higher-rank types are allowed.
test_IdRank2 :: TestTree
test_IdRank2 =
  testCase "IdRank2" $ do
    let res = mkConstant @Integer @DefaultUni () 0
        -- > sum (idRank2 {list} nil {integer})
        term =
          apply () (mapFun Left Scott.sum)
            . tyInst () (apply () (tyInst () (builtin () $ Right IdRank2) Scott.listTy) Scott.nil)
            $ integer
    typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term
      @?= Right (EvaluationSuccess res)

-- | Test that a builtin can be applied to a non-constant term.
test_ScottToMetaUnit :: TestTree
test_ScottToMetaUnit =
  testCase "ScottToMetaUnit" $ do
    let res = EvaluationSuccess $ mkConstant @() @DefaultUni () ()
        applyTerm = apply () (builtin () ScottToMetaUnit)
    -- @scottToMetaUnit Scott.unitval@ is well-typed and runs successfully.
    typecheckEvaluateCekNoEmit def () (applyTerm Scott.unitval) @?= Right res
    let runtime =
          MachineParameters def . mkMachineVariantParameters def $
            CostModel defaultCekMachineCostsForTesting ()
    -- @scottToMetaUnit Scott.map@ is ill-typed, but still runs successfully, since the builtin
    -- doesn't look at the argument.
    unsafeSplitStructuralOperational (evaluateCekNoEmit runtime (eraseTerm $ applyTerm Scott.map))
      @?= res

{-| Test that an exception thrown in the builtin application code does not get caught in the CEK
machine and blows in the caller face instead. Uses a one-argument built-in function. -}
test_FailingSucc :: TestTree
test_FailingSucc =
  testCase "FailingSucc" $ do
    let term =
          apply () (builtin () $ Right FailingSucc) $
            mkConstant @Integer @DefaultUni @DefaultFunExt () 0
    typeErrOrEvalExcOrRes :: Either _ (Either BuiltinErrorCall _) <-
      -- Here we rely on 'typecheckAnd' lazily running the action after type checking the
      -- term.
      traverse (try . evaluate) $
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term
    typeErrOrEvalExcOrRes @?= Right (Left BuiltinErrorCall)

{-| Test that evaluating a PLC builtin application that is expensive enough to exceed the budget
does not result in actual evaluation of the application on the Haskell side and instead we get an
'EvaluationFailure'. Uses a one-argument built-in function. -}
test_ExpensiveSucc :: TestTree
test_ExpensiveSucc =
  testCase "ExpensiveSucc" $ do
    let term =
          apply () (builtin () $ Right ExpensiveSucc) $
            mkConstant @Integer @DefaultUni @DefaultFunExt () 0
    typeErrOrEvalExcOrRes :: Either _ (Either BuiltinErrorCall _) <-
      traverse (try . evaluate) $
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term
    typeErrOrEvalExcOrRes @?= Right (Right EvaluationFailure)

{-| Test that an exception thrown in the builtin application code does not get caught in the CEK
machine and blows in the caller face instead. Uses a two-arguments built-in function. -}
test_FailingPlus :: TestTree
test_FailingPlus =
  testCase "FailingPlus" $ do
    let term =
          mkIterAppNoAnn
            (builtin () $ Right FailingPlus)
            [ mkConstant @Integer @DefaultUni @DefaultFunExt () 0
            , mkConstant @Integer @DefaultUni () 1
            ]
    typeErrOrEvalExcOrRes :: Either _ (Either BuiltinErrorCall _) <-
      -- Here we rely on 'typecheckAnd' lazily running the action after type checking the
      -- term.
      traverse (try . evaluate) $
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term
    typeErrOrEvalExcOrRes @?= Right (Left BuiltinErrorCall)

{-| Test that evaluating a PLC builtin application that is expensive enough to exceed the budget
does not result in actual evaluation of the application on the Haskell side and instead we get an
'EvaluationFailure'. Uses a two-arguments built-in function. -}
test_ExpensivePlus :: TestTree
test_ExpensivePlus =
  testCase "ExpensivePlus" $ do
    let term =
          mkIterAppNoAnn
            (builtin () $ Right ExpensivePlus)
            [ mkConstant @Integer @DefaultUni @DefaultFunExt () 0
            , mkConstant @Integer @DefaultUni () 1
            ]
    typeErrOrEvalExcOrRes :: Either _ (Either BuiltinErrorCall _) <-
      traverse (try . evaluate) $
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term
    typeErrOrEvalExcOrRes @?= Right (Right EvaluationFailure)

-- | Test that @Null@, @Head@ and @Tail@ are enough to get pattern matching on built-in lists.
test_BuiltinList :: TestTree
test_BuiltinList =
  testGroup "BuiltinList" $
    enumerate <&> \optMatch ->
      testCase (show optMatch) $ do
        let xs = [1 .. 10]
            res = mkConstant @Integer @DefaultUni () $ foldr (-) 0 xs
            term =
              mkIterAppNoAnn
                (mkIterInstNoAnn (Builtin.foldrList optMatch) [integer, integer])
                [ Builtin () SubtractInteger
                , mkConstant @Integer () 0
                , mkConstant @[Integer] () xs
                ]
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting term
          @?= Right (EvaluationSuccess res)

-- | Test that right-folding a built-in list with built-in 'Cons' recreates that list.
test_IdBuiltinList :: TestTree
test_IdBuiltinList =
  testGroup "IdBuiltinList" $
    enumerate <&> \optMatch ->
      testCase (show optMatch) $ do
        let xsTerm :: TermLike term tyname name DefaultUni DefaultFunExt => term ()
            xsTerm = mkConstant @[Integer] () [1 .. 10]
            listOfInteger = mkTyBuiltin @_ @[Integer] ()
            term =
              mkIterAppNoAnn
                ( mkIterInstNoAnn
                    (mapFun Left $ Builtin.foldrList optMatch)
                    [integer, listOfInteger]
                )
                [ tyInst () (builtin () $ Left MkCons) integer
                , mkConstant @[Integer] () []
                , xsTerm
                ]
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term
          @?= Right (EvaluationSuccess xsTerm)

test_BuiltinArray :: TestTree
test_BuiltinArray =
  testGroup
    "BuiltinArray"
    [ testCase "listToArray" do
        let listOfInts = mkConstant @[Integer] @DefaultUni () [1 .. 10]
        let arrayOfInts = mkConstant @(Vector Integer) @DefaultUni () (Vector.fromList [1 .. 10])
        let term = apply () (tyInst () (builtin () ListToArray) integer) listOfInts
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting term
          @?= Right (EvaluationSuccess arrayOfInts)
    , testCase "lengthOfArray" do
        let arrayOfInts = mkConstant @(Vector Integer) @DefaultUni () (Vector.fromList [1 .. 10])
        let expectedLength = mkConstant @Integer @DefaultUni () 10
            term = apply () (tyInst () (builtin () LengthOfArray) integer) arrayOfInts
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting term
          @?= Right (EvaluationSuccess expectedLength)
    , testCase "indexArray" do
        let arrayOfInts = mkConstant @(Vector Integer) @DefaultUni () (Vector.fromList [1 .. 10])
        let index = mkConstant @Integer @DefaultUni () 5
            expectedValue = mkConstant @Integer @DefaultUni () 6
            term = mkIterAppNoAnn (tyInst () (builtin () IndexArray) integer) [arrayOfInts, index]
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting term
          @?= Right (EvaluationSuccess expectedValue)
    ]

test_BuiltinPair :: TestTree
test_BuiltinPair =
  testCase "BuiltinPair" $ do
    let arg = mkConstant @(Integer, Bool) @DefaultUni () (1, False)
        inst efun = mkIterInstNoAnn (builtin () efun) [integer, bool]
        swapped = apply () (inst $ Right Swap) arg
        fsted = apply () (inst $ Left FstPair) arg
        snded = apply () (inst $ Left SndPair) arg
    -- > swap {integer} {bool} (1, False) ~> (False, 1)
    typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt swapped
      @?= Right (EvaluationSuccess $ mkConstant @(Bool, Integer) () (False, 1))
    -- > fst {integer} {bool} (1, False) ~> 1
    typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt fsted
      @?= Right (EvaluationSuccess $ mkConstant @Integer () 1)
    -- > snd {integer} {bool} (1, False) ~> False
    typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt snded
      @?= Right (EvaluationSuccess $ mkConstant @Bool () False)

test_SwapEls :: TestTree
test_SwapEls =
  testGroup "SwapEls" $
    enumerate <&> \optMatch ->
      testCase (show optMatch) $ do
        let xs = zip [1 .. 10] $ cycle [False, True]
            res =
              mkConstant @Integer @DefaultUni () $
                foldr (\p r -> r + (if snd p then -1 else 1) * fst p) 0 xs
            el = mkTyBuiltin @_ @(Integer, Bool) ()
            instProj p = mkIterInstNoAnn (builtin () p) [integer, bool]
            fun = runQuote $ do
              p <- freshName "p"
              r <- freshName "r"
              return
                . lamAbs () p el
                . lamAbs () r integer
                $ mkIterAppNoAnn
                  (builtin () AddInteger)
                  [ Var () r
                  , mkIterAppNoAnn
                      (builtin () MultiplyInteger)
                      [ mkIterAppNoAnn
                          (tyInst () (builtin () IfThenElse) integer)
                          [ apply () (instProj SndPair) $ Var () p
                          , mkConstant @Integer () (-1)
                          , mkConstant @Integer () 1
                          ]
                      , apply () (instProj FstPair) $ Var () p
                      ]
                  ]
            term =
              mkIterAppNoAnn
                (mkIterInstNoAnn (Builtin.foldrList optMatch) [el, integer])
                [ fun
                , mkConstant @Integer () 0
                , mkConstant () xs
                ]
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting term
          @?= Right (EvaluationSuccess res)

{-| Test that right-folding a built-in 'Data' with the constructors of 'Data' recreates the
original value. -}
test_IdBuiltinData :: TestTree
test_IdBuiltinData =
  testGroup "IdBuiltinData" $
    enumerate <&> \optMatch ->
      testCase (show optMatch) $ do
        let dTerm :: TermLike term tyname name DefaultUni fun => term ()
            dTerm =
              mkConstant @Data () $
                Map [(I 42, Constr 4 [List [B "abc", Constr 2 []], I 0])]
            emb = builtin () . Left
            term =
              mkIterAppNoAnn
                (ofoldrData optMatch)
                [ emb ConstrData
                , emb MapData
                , emb ListData
                , emb IData
                , emb BData
                , dTerm
                ]
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term
          @?= Right (EvaluationSuccess dTerm)

{-| For testing how an evaluator instantiated at a particular 'ExBudgetMode' handles the
'TrackCosts' builtin. -}
test_TrackCostsWith
  :: String -> Int -> (Term TyName Name DefaultUni ExtensionFun () -> IO ()) -> TestTree
test_TrackCostsWith cat len checkTerm =
  testCase ("TrackCosts: " ++ cat) $ do
    let term =
          apply () (builtin () TrackCosts) $
            mkConstant @Data () (List . replicate len $ I 42)
    checkTerm term

-- | Test that individual budgets are picked up by GC while spending is still ongoing.
test_TrackCostsRestricting :: TestTree
test_TrackCostsRestricting =
  let n = 10000
   in test_TrackCostsWith "restricting" n $ \term ->
        case typecheckReadKnownCek def () term of
          Left err -> fail $ displayPlc err
          Right (Left err) -> fail $ displayPlc err
          Right (Right (res :: [Integer])) -> do
            let expected = n `div` 10
                actual = length res
                err =
                  concat
                    [ "Too few elements picked up by GC\n"
                    , "Expected at least: " ++ show expected ++ "\n"
                    , "But got: " ++ show actual
                    ]
            assertBool err $ expected < actual

test_TrackCostsRetaining :: TestTree
test_TrackCostsRetaining =
  test_TrackCostsWith "retaining" 10000 $ \term -> do
    let
      -- An 'ExBudgetMode' that retains all the individual budgets by sticking them into a
      -- 'DList'.
      retaining = monoidalBudgeting $ const DList.singleton
      typecheckAndRunRetainer = typecheckAnd def $ \params term' ->
        let (getRes, budgets) = runCekNoEmit params retaining term'
         in (getRes >>= readKnownSelf, budgets)
    case typecheckAndRunRetainer () term of
      Left err -> fail $ displayPlc err
      Right (Left err, _) -> fail $ displayPlc err
      Right (Right (res :: [Integer]), budgets) -> do
        -- @length budgets@ is for retaining @budgets@ for as long as possible just in case.
        -- @3@ is just for giving us room to handle erratic GC behavior. It really should be
        -- @1@.
        let expected = min 5 (length budgets)
            actual = length res
            err =
              concat
                [ "Too many elements picked up by GC\n"
                , "Expected at most: " ++ show expected ++ "\n"
                , "But got: " ++ show actual ++ "\n"
                , "The result was: " ++ show res
                ]
        assertBool err $ expected > actual

typecheckAndEvalToOutOfEx :: Term TyName Name DefaultUni DefaultFun () -> Assertion
typecheckAndEvalToOutOfEx term =
  let evalRestricting params = fst . runCekNoEmit params restrictingLarge
   in case typecheckAnd def evalRestricting defaultBuiltinCostModelForTesting term of
        Right (Left (ErrorWithCause (OperationalError (CekOutOfExError _)) _)) ->
          pure ()
        err -> assertFailure $ "Expected a 'CekOutOfExError' but got: " ++ displayPlc err

test_SerialiseDataImpossible :: TestTree
test_SerialiseDataImpossible =
  testCase "Serialising an impossible 'Data' object runs out of budget and finishes" $ do
    let dataLoop :: Term TyName Name DefaultUni DefaultFun ()
        dataLoop =
          let loop = List [loop]
           in Apply () (Builtin () SerialiseData) $ mkConstant () loop
    typecheckAndEvalToOutOfEx dataLoop

test_fixId :: TestTree
test_fixId =
  testCase "'fix id' runs out of budget and finishes" $ do
    let fixId :: Term TyName Name DefaultUni DefaultFun ()
        fixId =
          mkIterAppNoAnn
            (mkIterInstNoAnn Plc.fix [integer, integer])
            [ tyInst () Plc.idFun (TyFun () integer integer)
            , mkConstant @Integer () 42
            ]
    typecheckAndEvalToOutOfEx fixId

{-| If the first char is an opening paren and the last chat is a closing paren, then remove them.
This is useful for rendering a term-as-a-test-name in CLI, since currently we wrap readably
pretty-printed terms in parens (which is to be fixed). -}
stripParensIfAny :: String -> String
stripParensIfAny str@('(' : str1) | last str == ')' = init str1
stripParensIfAny str = str

{-| Apply a built-in function to type then term arguments, evaluate that expression and expect
evaluation to succeed and return the given @a@ value. -}
evals
  :: DefaultUni `HasTermLevel` a
  => a
  -> DefaultFun
  -> [Type TyName DefaultUni ()]
  -> [Term TyName Name DefaultUni DefaultFun ()]
  -> TestNested
evals expectedVal fun typeArgs termArgs =
  let actualExpNoTermArgs = mkIterInstNoAnn (builtin () fun) typeArgs
      actualExp = mkIterAppNoAnn actualExpNoTermArgs termArgs
      prename = stripParensIfAny . render $ prettyPlcReadable actualExp
      -- Shorten the name of the test in case it's too long to be displayed in CLI.
      name =
        if length prename < 70
          then prename
          else
            stripParensIfAny (render $ prettyPlcReadable actualExpNoTermArgs)
              ++ concatMap (\_ -> " <...>") termArgs
      expectedRes = Right . EvaluationSuccess $ cons expectedVal
      actualRes = typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting actualExp
   in testNestedM name . embed . testCase "type checks and evaluates as expected" $
        expectedRes @=? actualRes

{-| Apply a built-in function to type then term arguments, evaluate that expression and expect
evaluation to fail. The logs along with the error are printed to a golden file. -}
fails
  :: String
  -- ^ Name of the golden file.
  -> DefaultFun
  -> [Type TyName DefaultUni ()]
  -> [Term TyName Name DefaultUni DefaultFun ()]
  -> TestNested
fails fileName fun typeArgs termArgs = do
  let actualExpNoTermArgs = mkIterInstNoAnn (builtin () fun) typeArgs
      actualExp = mkIterAppNoAnn actualExpNoTermArgs termArgs
      expectedToDisplay = "type checks and fails evaluation as expected"
  case typecheckAnd def (evaluateCek logEmitter) defaultBuiltinCostModelForTesting actualExp of
    Left err ->
      embed . testCase "type checks as expected" $
        assertFailure $
          displayPlcCondensedErrorClassic err
    Right (actualRes, logs) -> case actualRes of
      Right _ ->
        embed . testCase expectedToDisplay $
          assertFailure "expected an evaluation failure, but got a success"
      Left err ->
        let prename = stripParensIfAny . render $ prettyPlcReadable actualExp
            -- Shorten the name of the test in case it's too long to be displayed in CLI.
            name =
              if length prename < 70
                then prename
                else
                  stripParensIfAny (render $ prettyPlcReadable actualExpNoTermArgs)
                    ++ concatMap (\_ -> " <...>") termArgs
         in testNestedNamedM mempty name $
              testNestedNamedM mempty expectedToDisplay $
                nestedGoldenVsDoc fileName ".err" . vsep $
                  concat
                    [ [prettyPlcReadable err]
                    , ["Logs were:" | not $ null logs]
                    , map pretty logs
                    ]

-- | Test all integer related builtins
test_Integer :: TestNested
test_Integer = testNestedM "Integer" $ do
  evals @Integer 3 AddInteger [] [cons @Integer 2, cons @Integer 1]
  evals @Integer 2 SubtractInteger [] [cons @Integer 100, cons @Integer 98]
  evals @Integer (-2) SubtractInteger [] [cons @Integer 98, cons @Integer 100]
  evals @Integer 9702 MultiplyInteger [] [cons @Integer 99, cons @Integer 98]
  evals @Integer (-3) DivideInteger [] [cons @Integer 99, cons @Integer (-34)]
  evals @Integer (-2) QuotientInteger [] [cons @Integer 99, cons @Integer (-34)]
  evals @Integer 31 RemainderInteger [] [cons @Integer 99, cons @Integer (-34)]
  evals @Integer (-3) ModInteger [] [cons @Integer 99, cons @Integer (-34)]
  evals True LessThanInteger [] [cons @Integer 30, cons @Integer 4000]
  evals False LessThanInteger [] [cons @Integer 40, cons @Integer 40]
  evals True LessThanEqualsInteger [] [cons @Integer 30, cons @Integer 4000]
  evals True LessThanEqualsInteger [] [cons @Integer 4000, cons @Integer 4000]
  evals False LessThanEqualsInteger [] [cons @Integer 4001, cons @Integer 4000]
  evals True EqualsInteger [] [cons @Integer (-101), cons @Integer (-101)]
  evals False EqualsInteger [] [cons @Integer 0, cons @Integer 1]
  for_ [DivideInteger, QuotientInteger, ModInteger, RemainderInteger] $ \b ->
    fails (lowerInitialChar $ show b <> "-div-by-zero") b [] [cons @Integer 1, cons @Integer 0]
  test_ExpModInteger

test_ExpModInteger :: TestNested
test_ExpModInteger = testNestedM "ExpMod" $ do
  evals @Integer 1 b [] [int 500, zero, int 500] -- base:X, exp: zero, mod: X(strictpos)
  evals @Integer 0 b [] [int 500, int 5, int 500] -- base:X, exp: strictpos, mod: X(strictpos)
  evals @Integer 1 b [] [one, int (-3), int 4] -- base:1, exp: * , mod: strictpos
  evals @Integer 2 b [] [int 2, int (-3), int 3] -- base:*, exp: neg, mod: prime
  -- base is co-prime with mod and exponent is negative
  evals @Integer 4 b [] [int 4, int (-5), int 9]
  -- Always return 0 when modulus is 1.
  evals @Integer 0 b [] [zero, zero, one] -- base:0, exp: zero, mod:1
  evals @Integer 0 b [] [zero, one, one] -- base:0, exp: 1, mod:1
  evals @Integer 0 b [] [zero, int (-1), one] -- base:0, exp: neg, mod:1
  evals @Integer 0 b [] [int 500, int 222, one] -- base:*, exp: strictpos, mod:1
  evals @Integer 0 b [] [int 500, int (-1777), one] -- base:*, exp: neg, mod:1
  fails "mod-zero" b [] [one, one, zero] -- base:*, exp:*, mod: 0
  fails "mod-neg" b [] [one, one, int (-3)] -- base:*, exp:*, mod: neg
  -- base is zero, negative exponent
  fails "exp-neg-non-inverse0" b [] [int 0, int (-1), int 7]
  -- base and mod are not co-prime, negative exponent
  fails "exp-neg-non-inverse1" b [] [int 2, int (-3), int 4]
  -- mod is prime, but base&mod are not co-prime, negative exponent
  fails "exp-neg-non-inverse2" b [] [int 500, int (-5), int 5]
  where
    int = cons @Integer
    zero = int 0
    one = int 1
    b = ExpModInteger

-- | Test all string-like builtins
test_String :: TestNested
test_String = testNestedM "String" $ do
  -- bytestrings
  evals @ByteString "hello world" AppendByteString [] [cons @ByteString "hello", cons @ByteString " world"]
  evals @ByteString "mpla" AppendByteString [] [cons @ByteString "", cons @ByteString "mpla"]
  evals False EqualsByteString [] [cons @ByteString "", cons @ByteString "mpla"]
  evals True EqualsByteString [] [cons @ByteString "mpla", cons @ByteString "mpla"]
  evals True LessThanByteString [] [cons @ByteString "", cons @ByteString "mpla"]

  -- strings
  evals @Text "mpla" AppendString [] [cons @Text "", cons @Text "mpla"]
  evals False EqualsString [] [cons @Text "", cons @Text "mpla"]
  evals True EqualsString [] [cons @Text "mpla", cons @Text "mpla"]
  evals @Text "hello world" AppendString [] [cons @Text "hello", cons @Text " world"]

  -- id for subset char8 of utf8
  evals @ByteString "hello world" EncodeUtf8 [] [cons @Text "hello world"]
  evals @Text "hello world" DecodeUtf8 [] [cons @ByteString "hello world"]

  -- the 'o's replaced with greek o's, so they are kind of "invisible"
  evals @ByteString "hell\206\191 w\206\191rld" EncodeUtf8 [] [cons @Text "hellο wοrld"]
  -- cannot decode back, because bytestring only works on Char8 subset of utf8
  evals @Text "hellο wοrld" DecodeUtf8 [] [cons @ByteString "hell\206\191 w\206\191rld"]

  evals @ByteString "\NULhello world" ConsByteString [] [cons @Integer 0, cons @ByteString "hello world"]
  -- cannot overflow back to 0
  fails
    "consByteString-out-of-range"
    ConsByteString
    []
    [cons @Integer 256, cons @ByteString "hello world"]
  evals @ByteString "\240hello world" ConsByteString [] [cons @Integer 240, cons @ByteString "hello world"]
  -- 65 is ASCII A
  evals @ByteString "Ahello world" ConsByteString [] [cons @Integer 65, cons @ByteString "hello world"]

  evals @ByteString "h" SliceByteString [] [cons @Integer 0, cons @Integer 1, cons @ByteString "hello world"]
  evals @ByteString "he" SliceByteString [] [cons @Integer 0, cons @Integer 2, cons @ByteString "hello world"]
  evals @ByteString "el" SliceByteString [] [cons @Integer 1, cons @Integer 2, cons @ByteString "hello world"]
  evals @ByteString "world" SliceByteString [] [cons @Integer 6, cons @Integer 5, cons @ByteString "hello world"]

  evals @Integer 11 LengthOfByteString [] [cons @ByteString "hello world"]
  evals @Integer 0 LengthOfByteString [] [cons @ByteString ""]
  evals @Integer 1 LengthOfByteString [] [cons @ByteString "\NUL"]

  -- 65 is ASCII A
  evals @Integer 65 IndexByteString [] [cons @ByteString "Ahello world", cons @Integer 0]
  fails
    "indexByteString-out-of-bounds-non-empty"
    IndexByteString
    []
    [cons @ByteString "hello world", cons @Integer 12]
  fails
    "indexByteString-out-of-bounds-empty"
    IndexByteString
    []
    [cons @ByteString "", cons @Integer 0]

test_MatchList :: MatchOption -> TestNested
test_MatchList optMatch = testNestedM "MatchList" $ do
  let
    -- the null function that utilizes the ChooseList builtin (through the matchList helper
    -- function)
    nullViaMatch :: [Integer] -> Term TyName Name DefaultUni DefaultFun ()
    nullViaMatch l =
      mkIterAppNoAnn
        ( tyInst
            ()
            (apply () (tyInst () (Builtin.matchList optMatch) integer) $ cons l)
            bool
        )
        [ -- zero
          true
        , -- cons
          runQuote $ do
            a1 <- freshName "a1"
            a2 <- freshName "a2"
            pure
              . lamAbs () a1 integer
              . lamAbs () a2 (TyApp () Builtin.list integer)
              $ false
        ]

  embed . testCase "nullViaMatch []" $
    Right (EvaluationSuccess true)
      @=? typecheckEvaluateCekNoEmit
        def
        defaultBuiltinCostModelForTesting
        (nullViaMatch [])
  embed . testCase "nullViaMatch [1]" $
    Right (EvaluationSuccess false)
      @=? typecheckEvaluateCekNoEmit
        def
        defaultBuiltinCostModelForTesting
        (nullViaMatch [1])
  embed . testCase "nullViaMatch [1..10]" $
    Right (EvaluationSuccess false)
      @=? typecheckEvaluateCekNoEmit
        def
        defaultBuiltinCostModelForTesting
        (nullViaMatch [1 .. 10])

-- | Test all list-related builtins
test_List :: TestNested
test_List = testNestedM "List" $ do
  evals False NullList [integer] [cons @[Integer] [1, 2]]
  evals False NullList [integer] [cons @[Integer] [1]]
  evals True NullList [integer] [cons @[Integer] []]

  evals @Integer 1 HeadList [integer] [cons @[Integer] [1, 3]]
  evals @[Integer] [3, 4, 5] TailList [integer] [cons @[Integer] [1, 3, 4, 5]]

  fails "headList-empty" HeadList [integer] [cons @[Integer] []]
  fails "tailList-empty" TailList [integer] [cons @[Integer] []]

  evals @[Integer] [1] MkCons [integer] [cons @Integer 1, cons @[Integer] []]
  evals @[Integer] [1, 2] MkCons [integer] [cons @Integer 1, cons @[Integer] [2]]

  testNested "MatchList" $ map test_MatchList enumerate

test_MatchData :: TestNested
test_MatchData = testNestedM "MatchData" $ do
  let actualExp =
        mkIterAppNoAnn
          (tyInst () (apply () matchData $ cons $ I 3) bool)
          [ -- constr
            runQuote $ do
              a1 <- freshName "a1"
              a2 <- freshName "a2"
              pure $ lamAbs () a1 integer $ lamAbs () a2 (TyApp () Builtin.list dataTy) false
          , -- map
            runQuote $ do
              a1 <- freshName "a1"
              let listDataData = TyApp () Builtin.list $ mkIterTyAppNoAnn pair [dataTy, dataTy]
              pure $ lamAbs () a1 listDataData false
          , -- list
            runQuote $ do
              a1 <- freshName "a1"
              pure $ lamAbs () a1 (TyApp () Builtin.list dataTy) false
          , -- I
            runQuote $ do
              a1 <- freshName "a1"
              pure $ lamAbs () a1 integer true
          , -- B
            runQuote $ do
              a1 <- freshName "a1"
              pure $ lamAbs () a1 (mkTyBuiltin @_ @ByteString ()) false
          ]

  embed . testCase "chooseData" $
    Right (EvaluationSuccess true)
      @=? typecheckEvaluateCekNoEmit
        def
        defaultBuiltinCostModelForTesting
        actualExp

-- | Test all PlutusData builtins
test_Data :: TestNested
test_Data = testNestedM "Data" $ do
  -- construction
  evals (Constr 2 [I 3]) ConstrData [] [cons @Integer 2, cons @[Data] [I 3]]
  evals (Constr 2 [I 3, B ""]) ConstrData [] [cons @Integer 2, cons @[Data] [I 3, B ""]]
  evals (List []) ListData [] [cons @[Data] []]
  evals (List [I 3, B ""]) ListData [] [cons @[Data] [I 3, B ""]]
  evals (Map []) MapData [] [cons @[(Data, Data)] []]
  evals (Map [(I 3, B "")]) MapData [] [cons @[(Data, Data)] [(I 3, B "")]]
  evals (B "hello world") BData [] [cons @ByteString "hello world"]
  evals (I 3) IData [] [cons @Integer 3]
  evals (B "hello world") BData [] [cons @ByteString "hello world"]
  evals @[Data] [] MkNilData [] [cons ()]
  evals @[(Data, Data)] [] MkNilPairData [] [cons ()]

  -- equality
  evals True EqualsData [] [cons $ B "hello world", cons $ B "hello world"]
  evals True EqualsData [] [cons $ I 4, cons $ I 4]
  evals False EqualsData [] [cons $ B "hello world", cons $ I 4]
  evals True EqualsData [] [cons $ Constr 3 [I 4], cons $ Constr 3 [I 4]]
  evals False EqualsData [] [cons $ Constr 3 [I 3, B ""], cons $ Constr 3 [I 3]]
  evals False EqualsData [] [cons $ Constr 2 [I 4], cons $ Constr 3 [I 4]]
  evals True EqualsData [] [cons $ Map [(I 3, B "")], cons $ Map [(I 3, B "")]]
  evals False EqualsData [] [cons $ Map [(I 3, B "")], cons $ Map []]
  evals False EqualsData [] [cons $ Map [(I 3, B "")], cons $ Map [(I 3, B ""), (I 4, I 4)]]

  -- destruction
  evals @Integer 3 UnIData [] [cons $ I 3]
  evals @ByteString "hello world" UnBData [] [cons $ B "hello world"]
  evals @Integer 3 UnIData [] [cons $ I 3]
  evals @(Integer, [Data]) (1, []) UnConstrData [] [cons $ Constr 1 []]
  evals @(Integer, [Data]) (1, [I 3]) UnConstrData [] [cons $ Constr 1 [I 3]]
  evals @[(Data, Data)] [] UnMapData [] [cons $ Map []]
  evals @[(Data, Data)] [(B "", I 3)] UnMapData [] [cons $ Map [(B "", I 3)]]
  evals @[Data] [] UnListData [] [cons $ List []]
  evals @[Data] [I 3, I 4, B ""] UnListData [] [cons $ List [I 3, I 4, B ""]]
  evals @ByteString "\162\ETX@Ehello8c" SerialiseData [] [cons $ Map [(I 3, B ""), (B "hello", I $ -100)]]

  test_MatchData

-- | Test all cryptography-related builtins
test_Crypto :: TestNested
test_Crypto = testNestedM "Crypto" $ do
  evals
    True
    VerifyEd25519Signature
    []
    [ -- pubkey
      cons @ByteString "Y\218\215\204>\STX\233\152\251\243\158'm\130\&0\197\DEL\STXd\214`\147\243y(\234\167=kTj\164"
    , -- message
      cons @ByteString "hello world"
    , -- signature
      cons @ByteString "\a'\198\r\226\SYN;\bX\254\228\129n\131\177\193\DC3-k\249RriY\221wIL\240\144\r\145\195\191\196]\227\169U(\ETX\171\SI\199\163\138\160\128R\DC4\246n\142[g\SI\169\SUB\178\245\166\&0\243\b"
    ]

  evals
    False
    VerifyEd25519Signature
    []
    [ -- pubkey
      cons @ByteString "Y\218\215\204>\STX\233\152\251\243\158'm\130\&0\197\DEL\STXd\214`\147\243y(\234\167=kTj\164"
    , -- message
      cons @ByteString "HELLO WORLD"
    , -- signature
      cons @ByteString "\a'\198\r\226\SYN;\bX\254\228\129n\131\177\193\DC3-k\249RriY\221wIL\240\144\r\145\195\191\196]\227\169U(\ETX\171\SI\199\163\138\160\128R\DC4\246n\142[g\SI\169\SUB\178\245\166\&0\243\b"
    ]
  -- independently verified by `/usr/bin/sha256sum` with the hex output converted to ascii text
  -- sha256sum hex output: b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9
  evals @ByteString
    "\185M'\185\147M>\b\165.R\215\218}\171\250\196\132\239\227zS\128\238\144\136\247\172\226\239\205\233"
    Sha2_256
    []
    [cons @ByteString "hello world"]
  -- independently verified by `/usr/bin/sha3-256sum` with the hex output converted to ascii text
  -- sha3-256sum hex output: 644bcc7e564373040999aac89e7622f3ca71fba1d972fd94a31c3bfbf24e3938
  evals @ByteString
    "dK\204~VCs\EOT\t\153\170\200\158v\"\243\202q\251\161\217r\253\148\163\FS;\251\242N98"
    Sha3_256
    []
    [cons @ByteString "hello world"]
  -- independently verified by `/usr/bin/b2sum -l 256` with the hex output converted to ascii text
  -- b2sum -l 256 hex output: 256c83b297114d201b30179f3f0ef0cace9783622da5974326b436178aeef610
  evals @ByteString
    "%l\131\178\151\DC1M \ESC0\ETB\159?\SO\240\202\206\151\131b-\165\151C&\180\&6\ETB\138\238\246\DLE"
    Blake2b_256
    []
    [cons @ByteString "hello world"]
  -- independently verified by `/usr/bin/b2sum -l 224` with the hex output converted to ascii text
  -- b2sum -l 224 hex output: 42d1854b7d69e3b57c64fcc7b4f64171b47dff43fba6ac0499ff437f
  evals @ByteString
    "B\209\133K}i\227\181|d\252\199\180\246Aq\180}\255C\251\166\172\EOT\153\255C\DEL"
    Blake2b_224
    []
    [cons @ByteString "hello world"]
  -- independently verified by the calculator at `https://emn178.github.io/online-tools/keccak_256.html`
  -- with the hex output converted to ascii text
  -- hex output: 47173285a8d7341e5e972fc677286384f802f8ef42a5ec5f03bbfa254cb01fad
  evals @ByteString
    "G\ETB2\133\168\215\&4\RS^\151/\198w(c\132\248\STX\248\239B\165\236_\ETX\187\250%L\176\US\173"
    Keccak_256
    []
    [cons @ByteString "hello world"]
  -- independently verified by the calculator at https://emn178.github.io/online-tools/ripemd_160.html
  let
    hashHex = "98c615784ccb5fe5936fbc0cbe9dfdb408d92f0f"
    ripemd_160Hash = case Base16.decode $ Text.encodeUtf8 hashHex of
      Right res -> res
      Left _ -> error $ "Unexpected error during hex decoding: " <> Text.unpack hashHex
  evals @ByteString
    ripemd_160Hash
    Ripemd_160
    []
    [cons @ByteString "hello world"]
  -- Tests for blake2b_224: output obtained using the b2sum program from https://github.com/BLAKE2/BLAKE2
  evals
    ( pack
        [ 0x83
        , 0x6c
        , 0xc6
        , 0x89
        , 0x31
        , 0xc2
        , 0xe4
        , 0xe3
        , 0xe8
        , 0x38
        , 0x60
        , 0x2e
        , 0xca
        , 0x19
        , 0x02
        , 0x59
        , 0x1d
        , 0x21
        , 0x68
        , 0x37
        , 0xba
        , 0xfd
        , 0xdf
        , 0xe6
        , 0xf0
        , 0xc8
        , 0xcb
        , 0x07
        ]
    )
    Blake2b_224
    []
    [cons $ pack []]
  evals
    ( pack
        [ 0xfe
        , 0x57
        , 0xe0
        , 0x22
        , 0x87
        , 0x66
        , 0x2c
        , 0xe6
        , 0xe2
        , 0x9c
        , 0xba
        , 0x02
        , 0xca
        , 0x2f
        , 0x23
        , 0xc4
        , 0x1f
        , 0x20
        , 0x84
        , 0xc7
        , 0x95
        , 0x9f
        , 0x1c
        , 0xa3
        , 0xa5
        , 0x7e
        , 0xaf
        , 0x9e
        ]
    )
    Blake2b_224
    []
    [ cons $
        pack
          [ 0xfc
          , 0x56
          , 0xca
          , 0x9a
          , 0x93
          , 0x98
          , 0x2a
          , 0x46
          , 0x69
          , 0xcc
          , 0xab
          , 0xa6
          , 0xe3
          , 0xd1
          , 0x84
          , 0xa1
          , 0x9d
          , 0xe4
          , 0xce
          , 0x80
          , 0x0b
          , 0xb6
          , 0x43
          , 0xa3
          , 0x60
          , 0xc1
          , 0x45
          , 0x72
          , 0xae
          , 0xdb
          , 0x22
          , 0x97
          , 0x4f
          , 0x0c
          , 0x96
          , 0x6b
          , 0x85
          , 0x9d
          , 0x91
          , 0xad
          , 0x5d
          , 0x71
          , 0x3b
          , 0x7a
          , 0xd9
          , 0x99
          , 0x35
          , 0x79
          , 0x4d
          , 0x22 -- 400 bits
          -- Tests for blake2b_256: output obtained using the b2sum program from https://github.com/BLAKE2/BLAKE2
          ]
    ]

  evals
    ( pack
        [ 0x0e
        , 0x57
        , 0x51
        , 0xc0
        , 0x26
        , 0xe5
        , 0x43
        , 0xb2
        , 0xe8
        , 0xab
        , 0x2e
        , 0xb0
        , 0x60
        , 0x99
        , 0xda
        , 0xa1
        , 0xd1
        , 0xe5
        , 0xdf
        , 0x47
        , 0x77
        , 0x8f
        , 0x77
        , 0x87
        , 0xfa
        , 0xab
        , 0x45
        , 0xcd
        , 0xf1
        , 0x2f
        , 0xe3
        , 0xa8
        ]
    )
    Blake2b_256
    []
    [cons $ pack []]
  evals
    ( pack
        [ 0xfc
        , 0x63
        , 0xa3
        , 0xcd
        , 0xf1
        , 0xc9
        , 0xbe
        , 0xb0
        , 0x9e
        , 0x18
        , 0x98
        , 0x8a
        , 0x95
        , 0x7c
        , 0x58
        , 0x31
        , 0x98
        , 0xc7
        , 0xe3
        , 0x0f
        , 0xe4
        , 0x8b
        , 0x9e
        , 0x80
        , 0x41
        , 0xbb
        , 0x90
        , 0x4a
        , 0xf8
        , 0x78
        , 0x3b
        , 0x5c
        ]
    )
    Blake2b_256
    []
    [ cons $
        pack
          [ 0xfc
          , 0x56
          , 0xca
          , 0x9a
          , 0x93
          , 0x98
          , 0x2a
          , 0x46
          , 0x69
          , 0xcc
          , 0xab
          , 0xa6
          , 0xe3
          , 0xd1
          , 0x84
          , 0xa1
          , 0x9d
          , 0xe4
          , 0xce
          , 0x80
          , 0x0b
          , 0xb6
          , 0x43
          , 0xa3
          , 0x60
          , 0xc1
          , 0x45
          , 0x72
          , 0xae
          , 0xdb
          , 0x22
          , 0x97
          , 0x4f
          , 0x0c
          , 0x96
          , 0x6b
          , 0x85
          , 0x9d
          , 0x91
          , 0xad
          , 0x5d
          , 0x71
          , 0x3b
          , 0x7a
          , 0xd9
          , 0x99
          , 0x35
          , 0x79
          , 0x4d
          , 0x22 -- 400 bits
          -- Test vectors from ShortMsgKAT_256.txt in https://keccak.team/obsolete/KeccakKAT-3.zip.
          ]
    ]

  evals
    ( pack
        [ 0xC5
        , 0xD2
        , 0x46
        , 0x01
        , 0x86
        , 0xF7
        , 0x23
        , 0x3C
        , 0x92
        , 0x7E
        , 0x7D
        , 0xB2
        , 0xDC
        , 0xC7
        , 0x03
        , 0xC0
        , 0xE5
        , 0x00
        , 0xB6
        , 0x53
        , 0xCA
        , 0x82
        , 0x27
        , 0x3B
        , 0x7B
        , 0xFA
        , 0xD8
        , 0x04
        , 0x5D
        , 0x85
        , 0xA4
        , 0x70
        ]
    )
    Keccak_256
    []
    [cons $ pack []]
  evals
    ( pack
        [ 0xFA
        , 0x46
        , 0x0C
        , 0xD5
        , 0x1B
        , 0xC6
        , 0x11
        , 0x78
        , 0x6D
        , 0x36
        , 0x4F
        , 0xCA
        , 0xBE
        , 0x39
        , 0x05
        , 0x2B
        , 0xCD
        , 0x5F
        , 0x00
        , 0x9E
        , 0xDF
        , 0xA8
        , 0x1F
        , 0x47
        , 0x01
        , 0xC5
        , 0xB2
        , 0x2B
        , 0x72
        , 0x9B
        , 0x00
        , 0x16
        ]
    )
    Keccak_256
    []
    [ cons $
        pack
          [ 0x7E
          , 0x15
          , 0xD2
          , 0xB9
          , 0xEA
          , 0x74
          , 0xCA
          , 0x60
          , 0xF6
          , 0x6C
          , 0x8D
          , 0xFA
          , 0xB3
          , 0x77
          , 0xD9
          , 0x19
          , 0x8B
          , 0x7B
          , 0x16
          , 0xDE
          , 0xB6
          , 0xA1
          , 0xBA
          , 0x0E
          , 0xA3
          , 0xC7
          , 0xEE
          , 0x20
          , 0x42
          , 0xF8
          , 0x9D
          , 0x37
          , 0x86
          , 0xE7
          , 0x79
          , 0xCF
          , 0x05
          , 0x3C
          , 0x77
          , 0x78
          , 0x5A
          , 0xA9
          , 0xE6
          , 0x92
          , 0xF8
          , 0x21
          , 0xF1
          , 0x4A
          , 0x7F
          , 0x51 -- 400 bits
          -- Test vectors for sha2_256 from SHA256ShortMessage.rsp in
          -- https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip
          ]
    ]

  evals
    ( pack
        [ 0xe3
        , 0xb0
        , 0xc4
        , 0x42
        , 0x98
        , 0xfc
        , 0x1c
        , 0x14
        , 0x9a
        , 0xfb
        , 0xf4
        , 0xc8
        , 0x99
        , 0x6f
        , 0xb9
        , 0x24
        , 0x27
        , 0xae
        , 0x41
        , 0xe4
        , 0x64
        , 0x9b
        , 0x93
        , 0x4c
        , 0xa4
        , 0x95
        , 0x99
        , 0x1b
        , 0x78
        , 0x52
        , 0xb8
        , 0x55
        ]
    )
    Sha2_256
    []
    [cons $ pack []]
  evals
    ( pack
        [ 0x99
        , 0xdc
        , 0x77
        , 0x2e
        , 0x91
        , 0xea
        , 0x02
        , 0xd9
        , 0xe4
        , 0x21
        , 0xd5
        , 0x52
        , 0xd6
        , 0x19
        , 0x01
        , 0x01
        , 0x6b
        , 0x9f
        , 0xd4
        , 0xad
        , 0x2d
        , 0xf4
        , 0xa8
        , 0x21
        , 0x2c
        , 0x1e
        , 0xc5
        , 0xba
        , 0x13
        , 0x89
        , 0x3a
        , 0xb2
        ]
    )
    Sha2_256
    []
    [ cons $
        pack
          [ 0x3d
          , 0x83
          , 0xdf
          , 0x37
          , 0x17
          , 0x2c
          , 0x81
          , 0xaf
          , 0xd0
          , 0xde
          , 0x11
          , 0x51
          , 0x39
          , 0xfb
          , 0xf4
          , 0x39
          , 0x0c
          , 0x22
          , 0xe0
          , 0x98
          , 0xc5
          , 0xaf
          , 0x4c
          , 0x5a
          , 0xb4
          , 0x85
          , 0x24
          , 0x06
          , 0x51
          , 0x0b
          , 0xc0
          , 0xe6
          , 0xcf
          , 0x74
          , 0x17
          , 0x69
          , 0xf4
          , 0x44
          , 0x30
          , 0xc5
          , 0x27
          , 0x0f
          , 0xda
          , 0xe0
          , 0xcb
          , 0x84
          , 0x9d
          , 0x71
          , 0xcb
          , 0xab -- 400 bits
          -- Test vectors for sha3_256 from SHA3_256ShortMessage.rsp in
          -- https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bytetestvectors.zip
          ]
    ]

  evals
    ( pack
        [ 0xa7
        , 0xff
        , 0xc6
        , 0xf8
        , 0xbf
        , 0x1e
        , 0xd7
        , 0x66
        , 0x51
        , 0xc1
        , 0x47
        , 0x56
        , 0xa0
        , 0x61
        , 0xd6
        , 0x62
        , 0xf5
        , 0x80
        , 0xff
        , 0x4d
        , 0xe4
        , 0x3b
        , 0x49
        , 0xfa
        , 0x82
        , 0xd8
        , 0x0a
        , 0x4b
        , 0x80
        , 0xf8
        , 0x43
        , 0x4a
        ]
    )
    Sha3_256
    []
    [cons $ pack []]
  evals
    ( pack
        [ 0xe2
        , 0x18
        , 0x06
        , 0xce
        , 0x76
        , 0x6b
        , 0xbc
        , 0xe8
        , 0xb8
        , 0xd1
        , 0xb9
        , 0x9b
        , 0xcf
        , 0x16
        , 0x2f
        , 0xd1
        , 0x54
        , 0xf5
        , 0x46
        , 0x92
        , 0x35
        , 0x1a
        , 0xec
        , 0x8e
        , 0x69
        , 0x14
        , 0xe1
        , 0xa6
        , 0x94
        , 0xbd
        , 0xa9
        , 0xee
        ]
    )
    Sha3_256
    []
    [ cons $
        pack
          [ 0xfc
          , 0x56
          , 0xca
          , 0x9a
          , 0x93
          , 0x98
          , 0x2a
          , 0x46
          , 0x69
          , 0xcc
          , 0xab
          , 0xa6
          , 0xe3
          , 0xd1
          , 0x84
          , 0xa1
          , 0x9d
          , 0xe4
          , 0xce
          , 0x80
          , 0x0b
          , 0xb6
          , 0x43
          , 0xa3
          , 0x60
          , 0xc1
          , 0x45
          , 0x72
          , 0xae
          , 0xdb
          , 0x22
          , 0x97
          , 0x4f
          , 0x0c
          , 0x96
          , 0x6b
          , 0x85
          , 0x9d
          , 0x91
          , 0xad
          , 0x5d
          , 0x71
          , 0x3b
          , 0x7a
          , 0xd9
          , 0x99
          , 0x35
          , 0x79
          , 0x4d
          , 0x22 -- 400 bits
          ]
    ]

-- | Test that hashes produced by a hash function contain the expected number of bits
test_HashSize :: DefaultFun -> Integer -> TestTree
test_HashSize hashFun expectedNumBits =
  let testName = "HashSize " ++ show hashFun ++ " is " ++ show expectedNumBits ++ " bits"
      propName = fromString $ "HashSize " ++ show hashFun
   in testPropertyNamed
        testName
        propName
        . mapTestLimitAtLeast 10 (`div` 50)
        . property
        $ do
          bs <- forAll $ Gen.bytes (Range.linear 0 1000)
          let term =
                mkIterAppNoAnn
                  (builtin () MultiplyInteger)
                  [ cons @Integer 8
                  , mkIterAppNoAnn
                      (builtin () LengthOfByteString)
                      [mkIterAppNoAnn (builtin () hashFun) [cons @ByteString bs]]
                  ]
          typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting term === Right (EvaluationSuccess (cons @Integer expectedNumBits))

-- | Check that all hash functions return hashes with the correct number of bits
test_HashSizes :: TestTree
test_HashSizes =
  testGroup
    "Hash sizes"
    [ test_HashSize Sha2_256 256
    , test_HashSize Sha3_256 256
    , test_HashSize Blake2b_256 256
    , test_HashSize Keccak_256 256
    , test_HashSize Blake2b_224 224
    , test_HashSize Ripemd_160 160
    ]

-- Test all remaining builtins of the default universe
test_Other :: TestTree
test_Other = testCase "Other" $ do
  let expr1 = mkIterAppNoAnn (tyInst () (builtin () ChooseUnit) bool) [unitval, true]
  Right (EvaluationSuccess true) @=? typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting expr1

  let expr2 = mkIterAppNoAnn (tyInst () (builtin () IfThenElse) integer) [true, cons @Integer 1, cons @Integer 0]
  Right (EvaluationSuccess $ cons @Integer 1) @=? typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting expr2

  let expr3 = mkIterAppNoAnn (tyInst () (builtin () Trace) integer) [cons @Text "hello world", cons @Integer 1]
  Right (EvaluationSuccess $ cons @Integer 1) @=? typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting expr3

{-| Check that 'ExtensionVersion' evaluates correctly.
See Note [Builtin semantics variants] -}
test_Version :: TestTree
test_Version =
  testCase "Version" $ do
    let expr1 = apply () (builtin () $ Right ExtensionVersion) unitval
    Right (EvaluationSuccess $ cons @Integer 0)
      @=? typecheckEvaluateCekNoEmit
        (PairV @DefaultFun def ExtensionFunSemanticsVariant0)
        defaultBuiltinCostModelExt
        expr1
    Right
      ( EvaluationSuccess $
          cons @Integer $
            fromIntegral $
              fromEnum (maxBound :: BuiltinSemanticsVariant ExtensionFun)
      )
      @=? typecheckEvaluateCekNoEmit
        (PairV @DefaultFun def def)
        defaultBuiltinCostModelExt
        expr1

{-| Check that 'ConsByteString' wraps around for plutus' builtin-version == 1, and fails in plutus's builtin-versions >=2.
See Note [Builtin semantics variants] -}
test_ConsByteString :: TestTree
test_ConsByteString =
  testCase "ConsVersion" $ do
    let asciiBangWrapped =
          fromIntegral @Word8 @Integer maxBound
            + 1 -- to make word8 wraparound
            + 33 -- the index of '!' in ascii table
        expr1 =
          mkIterAppNoAnn
            (builtin () ConsByteString)
            [cons @Integer asciiBangWrapped, cons @ByteString "hello world"]
    for_ enumerate $ \case
      semVar@DefaultFunSemanticsVariantA ->
        Right (EvaluationSuccess $ cons @ByteString "!hello world")
          @=? typecheckEvaluateCekNoEmit semVar defaultBuiltinCostModelForTesting expr1
      semVar@DefaultFunSemanticsVariantB ->
        Right (EvaluationSuccess $ cons @ByteString "!hello world")
          @=? typecheckEvaluateCekNoEmit semVar defaultBuiltinCostModelForTesting expr1
      semVar@DefaultFunSemanticsVariantC ->
        Right EvaluationFailure
          @=? typecheckEvaluateCekNoEmit semVar defaultBuiltinCostModelForTesting expr1

-- shorthand
cons :: (DefaultUni `HasTermLevel` a, TermLike term tyname name DefaultUni fun) => a -> term ()
cons = mkConstant ()

-- Test that the SECP256k1 builtins are behaving correctly
test_SignatureVerification :: TestTree
test_SignatureVerification =
  testGroup
    "Signature verification"
    [ testGroup
        "Ed25519 signatures (VariantA)"
        [ testPropertyNamed
            "Ed25519_VariantA verification behaves correctly on all inputs"
            "ed25519_VariantA_correct"
            . mapTestLimitAtLeast 99 (`div` 10)
            $ property ed25519_VariantAProp
        ]
    , testGroup
        "Ed25519 signatures (VariantB)"
        [ testPropertyNamed
            "Ed25519_VariantB verification behaves correctly on all inputs"
            "ed25519_VariantB_correct"
            . mapTestLimitAtLeast 99 (`div` 10)
            $ property ed25519_VariantBProp
        ]
    , testGroup
        "Ed25519 signatures (VariantC)"
        [ testPropertyNamed
            "Ed25519_VariantC verification behaves correctly on all inputs"
            "ed25519_VariantC_correct"
            . mapTestLimitAtLeast 99 (`div` 10)
            $ property ed25519_VariantCProp
        ]
    , testGroup
        "Signatures on the SECP256k1 curve"
        [ testPropertyNamed
            "ECDSA verification behaves correctly on all inputs"
            "ecdsa_correct"
            . mapTestLimitAtLeast 99 (`div` 10)
            $ property ecdsaSecp256k1Prop
        , testPropertyNamed
            "Schnorr verification behaves correctly on all inputs"
            "schnorr_correct"
            . mapTestLimitAtLeast 99 (`div` 10)
            $ property schnorrSecp256k1Prop
        ]
    ]

-- Test that the Integer <-> ByteString conversion builtins are behaving correctly
test_Conversion :: TestTree
test_Conversion =
  testGroup
    "Integer <-> ByteString conversions"
    [ testGroup
        "Integer -> ByteString"
        [ --- lengthOfByteString (integerToByteString e d 0) = d
          testPropertyNamed "property 1" "i2b_prop1"
            . mapTestLimitAtLeast 99 (`div` 10)
            $ property Conversion.i2bProperty1
        , -- indexByteString (integerToByteString e k 0) j = 0
          testPropertyNamed "property 2" "i2b_prop2"
            . mapTestLimitAtLeast 99 (`div` 10)
            $ property Conversion.i2bProperty2
        , -- lengthOfByteString (integerToByteString e 0 p) > 0
          testPropertyNamed "property 3" "i2b_prop3"
            . mapTestLimitAtLeast 99 (`div` 10)
            $ property Conversion.i2bProperty3
        , -- integerToByteString False 0 (multiplyInteger p 256) = consByteString
          -- 0 (integerToByteString False 0 p)
          testPropertyNamed "property 4" "i2b_prop4"
            . mapTestLimitAtLeast 50 (`div` 20)
            $ property Conversion.i2bProperty4
        , -- integerToByteString True 0 (multiplyInteger p 256) = appendByteString
          -- (integerToByteString True 0 p) (singleton 0)
          testPropertyNamed "property 5" "i2b_prop5"
            . mapTestLimitAtLeast 50 (`div` 20)
            $ property Conversion.i2bProperty5
        , -- integerToByteString False 0 (plusInteger (multiplyInteger q 256) r) =
          -- appendByteString (integerToByteString False 0 r) (integerToByteString False 0 q)
          testPropertyNamed "property 6" "i2b_prop6"
            . mapTestLimitAtLeast 50 (`div` 20)
            $ property Conversion.i2bProperty6
        , -- integerToByteString True 0 (plusInteger (multiplyInteger q 256) r) =
          -- appendByteString (integerToByteString False 0 q)
          -- (integerToByteString False 0 r)
          testPropertyNamed "property 7" "i2b_prop7"
            . mapTestLimitAtLeast 50 (`div` 20)
            $ property Conversion.i2bProperty7
        , testGroup "CIP-121 examples" Conversion.i2bCipExamples
        , testGroup "Tests for integerToByteString size limit" Conversion.i2bLimitTests
        ]
    , testGroup
        "ByteString -> Integer"
        [ -- byteStringToInteger b (integerToByteString b d q) = q
          testPropertyNamed "property 1" "b2i_prop1"
            . mapTestLimitAtLeast 99 (`div` 10)
            $ property Conversion.b2iProperty1
        , -- byteStringToInteger b (consByteString w8 emptyByteString) = w8
          testPropertyNamed "property 2" "b2i_prop2"
            . mapTestLimitAtLeast 99 (`div` 10)
            $ property Conversion.b2iProperty2
        , -- integerToByteString b (lengthOfByteString bs) (byteStringToInteger b bs) = bs
          testPropertyNamed "property 3" "b2i_prop3"
            . mapTestLimitAtLeast 99 (`div` 10)
            $ property Conversion.b2iProperty3
        , testGroup "CIP-121 examples" Conversion.b2iCipExamples
        ]
    ]

-- Tests for the bitwise logical operations, as per [CIP-122](https://cips.cardano.org/cip/CIP-0122).
test_Bitwise_CIP0122 :: TestTree
test_Bitwise_CIP0122 =
  testGroup
    "Bitwise operations (CIP0122)"
    [ testGroup
        "andByteString"
        [ CIP0122.abelianSemigroupLaws "truncation" PLC.AndByteString False
        , CIP0122.idempotenceLaw "truncation" PLC.AndByteString False
        , CIP0122.absorbtionLaw "truncation" PLC.AndByteString False ""
        , CIP0122.leftDistributiveLaw "truncation" "itself" PLC.AndByteString PLC.AndByteString False
        , CIP0122.leftDistributiveLaw "truncation" "OR" PLC.AndByteString PLC.OrByteString False
        , CIP0122.leftDistributiveLaw "truncation" "XOR" PLC.AndByteString PLC.XorByteString False
        , CIP0122.abelianMonoidLaws "padding" PLC.AndByteString True ""
        , CIP0122.distributiveLaws "padding" PLC.AndByteString True
        ]
    , testGroup
        "orByteString"
        [ CIP0122.abelianSemigroupLaws "truncation" PLC.OrByteString False
        , CIP0122.idempotenceLaw "truncation" PLC.OrByteString False
        , CIP0122.absorbtionLaw "truncation" PLC.OrByteString False ""
        , CIP0122.leftDistributiveLaw "truncation" "itself" PLC.OrByteString PLC.OrByteString False
        , CIP0122.leftDistributiveLaw "truncation" "AND" PLC.OrByteString PLC.AndByteString False
        , CIP0122.abelianMonoidLaws "padding" PLC.OrByteString True ""
        , CIP0122.distributiveLaws "padding" PLC.OrByteString True
        ]
    , testGroup
        "xorByteString"
        [ CIP0122.abelianSemigroupLaws "truncation" PLC.XorByteString False
        , CIP0122.absorbtionLaw "truncation" PLC.XorByteString False ""
        , CIP0122.xorInvoluteLaw
        , CIP0122.abelianMonoidLaws "padding" PLC.XorByteString True ""
        ]
    , testGroup
        "complementByteString"
        [ CIP0122.complementSelfInverse
        , CIP0122.deMorgan
        ]
    , testGroup
        "bit reading and modification"
        [ CIP0122.getSet
        , CIP0122.setGet
        , CIP0122.setSet
        , CIP0122.writeBitsHomomorphismLaws
        ]
    , testGroup
        "replicateByte"
        [ CIP0122.replicateHomomorphismLaws
        , CIP0122.replicateIndex
        ]
    ]

-- Tests of the laws for the bitwise operations from [CIP-0123](https://cips.cardano.org/cip/CIP-0123).
test_Bitwise_CIP0123 :: TestTree
test_Bitwise_CIP0123 =
  testGroup
    "Bitwise operations (CIP0123)"
    [ testGroup
        "shiftByteString"
        [ testGroup "homomorphism" CIP0123.shiftHomomorphism
        , testPropertyNamed "shifts over bit length clear input" "shift_too_much" $
            mapTestLimitAtLeast 50 (`div` 20) CIP0123.shiftClear
        , testPropertyNamed "positive shifts clear low indexes" "shift_pos_low" $
            mapTestLimitAtLeast 99 (`div` 10) CIP0123.shiftPosClearLow
        , testPropertyNamed "negative shifts clear high indexes" "shift_neg_high" $
            mapTestLimitAtLeast 99 (`div` 10) CIP0123.shiftNegClearHigh
        , testPropertyNamed "shifts do not break when given minBound" "shift_min_bound" $
            mapTestLimitAtLeast 99 (`div` 10) CIP0123.shiftMinBound
        ]
    , testGroup
        "rotateByteString"
        [ testGroup "homomorphism" CIP0123.rotateHomomorphism
        , testPropertyNamed "rotations over bit length roll over" "rotate_too_much" $
            mapTestLimitAtLeast 50 (`div` 20) CIP0123.rotateRollover
        , testPropertyNamed "rotations move bits but don't change them" "rotate_move" $
            mapTestLimitAtLeast 50 (`div` 20) CIP0123.rotateMoveBits
        , testPropertyNamed "rotations do not break when given minBound" "rotate_min_bound" $
            mapTestLimitAtLeast 50 (`div` 20) CIP0123.rotateMinBound
        ]
    , testGroup
        "countSetBits"
        [ testGroup "homomorphism" CIP0123.csbHomomorphism
        , testPropertyNamed "rotation preserves count" "popcount_rotate" $
            mapTestLimitAtLeast 50 (`div` 20) CIP0123.csbRotate
        , testPropertyNamed "count of the complement" "popcount_complement" $
            mapTestLimitAtLeast 50 (`div` 20) CIP0123.csbComplement
        , testPropertyNamed "inclusion-exclusion" "popcount_inclusion_exclusion" $
            mapTestLimitAtLeast 50 (`div` 20) CIP0123.csbInclusionExclusion
        , testPropertyNamed "count of self-XOR" "popcount_self_xor" $
            mapTestLimitAtLeast 99 (`div` 10) CIP0123.csbXor
        ]
    , testGroup
        "findFirstSetBit"
        [ testPropertyNamed "find first in zero bytestrings" "ffs_zero" $
            mapTestLimitAtLeast 99 (`div` 10) CIP0123.ffsZero
        , testPropertyNamed "find first in replicated" "ffs_replicate" $
            mapTestLimitAtLeast 50 (`div` 20) CIP0123.ffsReplicate
        , testPropertyNamed "find first of self-XOR" "ffs_xor" $
            mapTestLimitAtLeast 99 (`div` 10) CIP0123.ffsXor
        , testPropertyNamed "found index set, lower indices clear" "ffs_index" $
            mapTestLimitAtLeast 50 (`div` 20) CIP0123.ffsIndex
        , testPropertyNamed "regression #6453 check" "regression_6453" $
            mapTestLimitAtLeast 99 (`div` 10) CIP0123.ffs6453
        ]
    ]

test_integer_properties :: TestTree
test_integer_properties =
  testGroup
    "test_integer_properties"
    [ test_integer_ring_properties
    , test_integer_div_mod_properties
    , test_integer_quot_rem_properties
    , test_integer_order_properties
    , test_integer_ring_properties
    , test_integer_exp_mod_properties
    ]

test_Case :: TestTree
test_Case =
  testGroup
    "Case on constants"
    [ QC.testProperty "Bool, 1 branch" . QC.withMaxSuccess 99 $
        \(scrut :: Bool) (i :: Integer) ->
          let term :: TermLike term tyname name DefaultUni DefaultFun => term ()
              term =
                kase
                  ()
                  (mkTyBuiltin @_ @Integer ())
                  (mkConstant () scrut)
                  [mkConstant () i]
           in case typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting term of
                Right (EvaluationSuccess res) -> res == mkConstant () i
                Right EvaluationFailure -> scrut
                _ -> False
    , QC.testProperty "Bool, 2 branches" . QC.withMaxSuccess 99 $
        \(scrut :: Bool) (i :: Integer) (j :: Integer) ->
          let term :: TermLike term tyname name DefaultUni DefaultFun => term ()
              term =
                kase
                  ()
                  (mkTyBuiltin @_ @Integer ())
                  (mkConstant () scrut)
                  [mkConstant () i, mkConstant () j]
           in Right (EvaluationSuccess . mkConstant () $ if not scrut then i else j)
                QC.=== typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting term
    , QC.testProperty "Bool, 3+ branches" . QC.withMaxSuccess 99 $
        \(scrut :: Bool) (is :: [Integer]) ->
          let term :: TermLike term tyname name DefaultUni DefaultFun => term ()
              term =
                kase
                  ()
                  (mkTyBuiltin @_ @Integer ())
                  (mkConstant () scrut)
                  (map (mkConstant ()) $ [1, 2, 3] <> is)
           in isLeft $ typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting term
    , QC.testProperty "Integer success" . QC.withMaxSuccess 99 $
        \(QC.NonEmpty is :: QC.NonEmptyList Integer) ->
          QC.forAll (QC.chooseInt (0, length is - 1)) $ \scrut ->
            let term :: TermLike term tyname name DefaultUni DefaultFun => term ()
                term =
                  kase
                    ()
                    (mkTyBuiltin @_ @Integer ())
                    (mkConstant () $ toInteger scrut)
                    (map (mkConstant ()) is)
             in Right (EvaluationSuccess . mkConstant () $ is !! scrut)
                  QC.=== typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting term
    , QC.testProperty "Integer any" . QC.withMaxSuccess 99 $
        \(scrut :: Integer) (is :: [Integer]) ->
          let term :: TermLike term tyname name DefaultUni DefaultFun => term ()
              term =
                kase
                  ()
                  (mkTyBuiltin @_ @Integer ())
                  (mkConstant () scrut)
                  (map (mkConstant ()) is)
           in case typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting term of
                Left _ -> False
                Right EvaluationFailure -> 0 > scrut || scrut >= fromIntegral (length is)
                Right (EvaluationSuccess res) -> res == mkConstant () (is !! fromIntegral scrut)
    , QC.testProperty "List, 1 branch" . QC.withMaxSuccess 99 $
        \(scrut :: [Integer]) ->
          let
            term :: Term TyName Name DefaultUni DefaultFun ()
            term = runQuote $ do
              x <- freshName "x"
              xs <- freshName "xs"
              let
                listElem = mkTyBuiltin @_ @Integer ()
                list = mkTyBuiltin @_ @[Integer] ()
              pure $
                kase
                  ()
                  listElem
                  (mkConstant () scrut)
                  [lamAbs () x listElem $ lamAbs () xs list $ var () x]
           in
            case (typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting term, scrut) of
              (Right (EvaluationSuccess res), (x : _)) -> res == mkConstant () x
              (Right EvaluationFailure, []) -> True
              _ -> False
    , QC.testProperty "List, 2 branches" . QC.withMaxSuccess 99 $
        \(scrut :: [Integer]) (i :: Integer) ->
          let
            term :: Term TyName Name DefaultUni DefaultFun ()
            term = runQuote $ do
              x <- freshName "x"
              xs <- freshName "xs"
              let
                listElem = mkTyBuiltin @_ @Integer ()
                list = mkTyBuiltin @_ @[Integer] ()
              pure $
                kase
                  ()
                  listElem
                  (mkConstant () scrut)
                  [ lamAbs () x listElem $ lamAbs () xs list $ var () x
                  , mkConstant @Integer () i
                  ]
           in
            case (typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting term, scrut) of
              (Right (EvaluationSuccess res), []) -> res == mkConstant () i
              (Right (EvaluationSuccess res), (x : _)) -> res == mkConstant () x
              _ -> False
    , QC.testProperty "List, 3+ branches" . QC.withMaxSuccess 99 $
        \(scrut :: [Integer]) (is :: [Integer]) ->
          let
            term :: Term TyName Name DefaultUni DefaultFun ()
            term =
              kase
                ()
                (mkTyBuiltin @_ @Integer ())
                (mkConstant () scrut)
                (map (mkConstant ()) $ [1, 2, 3] <> is)
           in
            isLeft $ typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting term
    ]

test_definition :: TestTree
test_definition =
  testGroup
    "definition"
    [ test_IntegerDistribution
    , test_Factorial
    , test_ForallFortyTwo
    , test_Const
    , test_Id
    , test_IdFInteger
    , test_IdList
    , test_IdRank2
    , test_ScottToMetaUnit
    , test_FailingSucc
    , test_ExpensiveSucc
    , test_FailingPlus
    , test_ExpensivePlus
    , test_BuiltinList
    , test_IdBuiltinList
    , test_BuiltinArray
    , test_BuiltinPair
    , test_SwapEls
    , test_IdBuiltinData
    , test_TrackCostsRestricting
    , ignoreTestWhenHpcEnabled test_TrackCostsRetaining
    , test_SerialiseDataImpossible
    , test_fixId
    , runTestNestedHere
        [ test_Integer
        , test_String
        , test_List
        , test_Data
        , test_Crypto
        ]
    , test_HashSizes
    , test_SignatureVerification
    , test_BLS12_381
    , test_integer_properties
    , test_Other
    , test_Version
    , test_ConsByteString
    , test_Conversion
    , test_Bitwise_CIP0122
    , test_Bitwise_CIP0123
    , test_Case
    ]
