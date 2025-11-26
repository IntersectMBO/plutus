-- editorconfig-checker-disable-file
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Evaluation.Machines
  ( test_machines
  , test_budget
  , test_tallying
  , test_NumberOfStepCounters
  ) where

import PlutusPrelude

import UntypedPlutusCore
import UntypedPlutusCore.Evaluation.Machine.Cek as Cek
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal (NumberOfStepCounters)
import UntypedPlutusCore.Evaluation.Machine.SteppableCek qualified as SCek

import PlutusCore qualified as Plc
import PlutusCore.Builtin
import PlutusCore.Compiler.Erase
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as Plc
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.FsTree
import PlutusCore.Generators.Hedgehog.Interesting
import PlutusCore.MkPlc
import PlutusCore.Pretty

import PlutusCore.Examples.Builtins
import PlutusCore.StdLib.Data.Nat qualified as Plc
import PlutusCore.StdLib.Meta
import PlutusCore.StdLib.Meta.Data.Function (etaExpand)

import Data.Proxy (Proxy (..))
import GHC.Exts (fromString)
import GHC.Ix
import GHC.TypeNats (natVal)
import Hedgehog hiding (Size, Var, eval)
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.Golden
import Test.Tasty.Hedgehog

testMachine
  :: (uni ~ DefaultUni, fun ~ DefaultFun, PrettyPlc structural)
  => String
  -> ( Term Name uni fun ()
       -> Either
            (EvaluationException structural operational (Term Name uni fun ()))
            (Term Name uni fun ())
     )
  -> TestTree
testMachine machine eval =
  testGroup machine $ fromInterestingTermGens $ \name genTermOfTbv ->
    testPropertyNamed name (fromString name) . withTests 99 . property $ do
      TermOf term val <- forAllWith mempty genTermOfTbv
      let resExp = makeKnownOrFail @_ @(Plc.Term TyName Name DefaultUni DefaultFun ()) val
      case splitStructuralOperational . eval $ eraseTerm term of
        Left err -> fail $ show err
        Right resAct -> resAct === fmap eraseTerm resExp

test_machines :: TestTree
test_machines =
  testGroup
    "machines"
    [ testMachine "CEK" $ Cek.evaluateCekNoEmit Plc.defaultCekParametersForTesting
    , testMachine "SteppableCEK" $ SCek.evaluateCekNoEmit Plc.defaultCekParametersForTesting
    ]

testBudget
  :: (Ix fun, Show fun, Hashable fun, Pretty fun, Typeable fun)
  => BuiltinsRuntime fun (CekValue DefaultUni fun ())
  -> TestName
  -> Term Name DefaultUni fun ()
  -> TestNested
testBudget runtime name term =
  nestedGoldenVsText
    name
    ".uplc"
    ( render $
        prettyPlcReadable $
          runCekNoEmit
            ( MachineParameters def $
                MachineVariantParameters Plc.defaultCekMachineCostsForTesting runtime
            )
            Cek.tallying
            term
    )

bunchOfFibs :: PlcFolderContents DefaultUni DefaultFun
bunchOfFibs = FolderContents [treeFolderContents "Fib" $ map fibFile [1 .. 3]]
  where
    fibFile i = plcTermFile (show i) (naiveFib i)

{-| To check how a sequence of calls to a built-in @id@ affects budgeting when a (relatively)
big AST is threaded through them. -}
bunchOfIdNats :: PlcFolderContents DefaultUni ExtensionFun
bunchOfIdNats =
  FolderContents [treeFolderContents "IdNat" $ map idNatFile [0 :: Int, 3 .. 9]]
  where
    idNatFile i = plcTermFile (show i) (idNat id0 i)
    -- > id0 = foldNat {nat} succ zero
    id0 = mkIterAppNoAnn (tyInst () Plc.foldNat $ Plc.natTy) [Plc.succ, Plc.zero]

    idNat idN 0 = apply () idN $ metaIntegerToNat 10
    idNat idN n = idNat idN' (n - 1)
      where
        -- Intentionally not eta-expanding the call to @idN'@, so that it gets forced during
        -- evaluation, which causes @idN@ to get forced, which on the first iteration causes
        -- @id0@ to get forced, which gives us a sufficiently big AST.
        -- > idN' = id {nat -> nat} idN
        idN' = apply () (tyInst () (builtin () Id) $ Plc.TyFun () Plc.natTy Plc.natTy) idN

-- | Same as 'bunchOfIdNats' except uses the built-in @ifThenElse@.
bunchOfIfThenElseNats :: PlcFolderContents DefaultUni DefaultFun
bunchOfIfThenElseNats =
  FolderContents [treeFolderContents "IfThenElse" $ map ifThenElseNatFile [0 :: Int, 1 .. 5]]
  where
    ifThenElseNatFile i = plcTermFile (show i) (ifThenElseNat id0 i)
    -- > id0 = foldNat {nat} succ zero
    id0 = mkIterAppNoAnn (tyInst () Plc.foldNat Plc.natTy) [Plc.succ, Plc.zero]

    ifThenElseNat idN 0 = apply () idN $ metaIntegerToNat 10
    ifThenElseNat idN n = ifThenElseNat idN' (n - 1)
      where
        -- Eta-expanding @idN'@ so that all of the if-then-else-s don't get evaluated --
        -- only those that are on the actual execution path.
        -- > idN' = \(n : nat) -> ifThenElse {nat -> nat} ($(even n)) idN idN n
        idN' =
          etaExpand Plc.natTy $
            mkIterAppNoAnn
              (tyInst () (builtin () IfThenElse) $ Plc.TyFun () Plc.natTy Plc.natTy)
              [mkConstant () $ even n, idN, idN]

test_budget :: TestTree
test_budget =
  -- Error diffs are very big
  localOption (SizeCutoff 1000000)
    . runTestNested ["untyped-plutus-core", "test", "Evaluation", "Machines", "Budget"]
    $ concat
      [ folder Plc.defaultBuiltinsRuntimeForTesting bunchOfFibs
      , folder (toBuiltinsRuntime def ()) bunchOfIdNats
      , folder Plc.defaultBuiltinsRuntimeForTesting bunchOfIfThenElseNats
      ]
  where
    folder runtime =
      foldPlcFolderContents testNested mempty (\name -> testBudget runtime name . eraseTerm)

testTallying :: TestName -> Term Name DefaultUni DefaultFun () -> TestNested
testTallying name term =
  nestedGoldenVsText
    name
    ".uplc"
    (render $ prettyPlcReadable $ runCekNoEmit Plc.defaultCekParametersForTesting Cek.tallying term)

test_tallying :: TestTree
test_tallying =
  -- Error diffs are very big
  localOption (SizeCutoff 1000000)
    . runTestNested ["untyped-plutus-core", "test", "Evaluation", "Machines", "Tallying"]
    . foldPlcFolderContents testNested mempty (\name -> testTallying name . eraseTerm)
    $ bunchOfFibs

test_NumberOfStepCounters :: TestTree
test_NumberOfStepCounters =
  runTestNestedM ["untyped-plutus-core", "test", "Evaluation", "Machines"] $ do
    nestedGoldenVsDoc "NumberOfStepCounters" "" . pretty . natVal $ Proxy @NumberOfStepCounters
    nestedGoldenVsDoc "NumberOfStepCounters" "" . pretty . length $ enumerate @StepKind
