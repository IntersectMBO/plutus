{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}

module Evaluation.Machines
    ( test_machines
    , test_memory
    , test_budget
    , test_tallying
    ) where

import           Language.UntypedPlutusCore
import           Language.UntypedPlutusCore.Evaluation.HOAS
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek as Cek

import qualified Language.PlutusCore                               as Plc
import           Language.PlutusCore.Builtins
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.FsTree
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Universe

import           Language.PlutusCore.Examples.Builtins
import           Language.PlutusCore.Examples.Everything           (examples)
import qualified Language.PlutusCore.StdLib.Data.Nat               as Plc
import           Language.PlutusCore.StdLib.Everything             (stdLib)
import           Language.PlutusCore.StdLib.Meta
import           Language.PlutusCore.StdLib.Meta.Data.Function     (etaExpand)

import           Common
import           Data.String
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Text
import           GHC.Ix
import           Hedgehog                                          hiding (Size, Var, eval)
import           Test.Tasty
import           Test.Tasty.Hedgehog

testMachine
    :: (uni ~ DefaultUni, fun ~ DefaultFun, PrettyPlc internal)
    => String
    -> (Term Name uni fun () ->
           Either (EvaluationException user internal (Term Name uni fun ())) (Term Name uni fun ()))
    -> TestTree
testMachine machine eval =
    testGroup machine $ fromInterestingTermGens $ \name genTermOfTbv ->
        testProperty name . withTests 200 . property $ do
            TermOf term val <- forAllWith mempty genTermOfTbv
            let resExp = erase <$> makeKnownNoEmit @(Plc.Term TyName Name DefaultUni DefaultFun ()) val
            case extractEvaluationResult . eval $ erase term of
                Left err     -> fail $ show err
                Right resAct -> resAct === resExp

test_machines :: TestTree
test_machines =
    testGroup "machines"
        [ testMachine "CEK"  $ evaluateCekNoEmit defBuiltinsRuntime
        , testMachine "HOAS" $ evaluateHoas defBuiltinsRuntime
        ]

testMemory :: ExMemoryUsage a => TestName -> a -> TestNested
testMemory name = nestedGoldenVsText name . fromString . show . memoryUsage

test_memory :: TestTree
test_memory =
    runTestNestedIn ["untyped-plutus-core", "test", "Evaluation", "Machines"]
        .  testNested "Memory"
        .  foldPlcFolderContents testNested testMemory testMemory
        $  stdLib
        <> examples

testBudget
    :: (Ix fun, Show fun, Pretty fun, Hashable fun, ExMemoryUsage fun)
    => BuiltinsRuntime fun (CekValue DefaultUni fun)
    -> TestName
    -> Term Name DefaultUni fun ()
    -> TestNested
testBudget runtime name term =
                       nestedGoldenVsText
    name
    (renderStrict $ layoutPretty defaultLayoutOptions {layoutPageWidth = AvailablePerLine maxBound 1.0} $
        prettyPlcReadableDef $ runCekNoEmit runtime Cek.tallying term)

bunchOfFibs :: PlcFolderContents DefaultUni DefaultFun
bunchOfFibs = FolderContents [treeFolderContents "Fib" $ map fibFile [1..3]] where
    fibFile i = plcTermFile (show i) (naiveFib i)

-- | To check how a sequence of calls to a built-in @id@ affects budgeting when a (relatively)
-- big AST is threaded through them.
bunchOfIdNats :: PlcFolderContents DefaultUni ExtensionFun
bunchOfIdNats =
    FolderContents [treeFolderContents "IdNat" $ map idNatFile [0 :: Int, 3.. 9]] where
        idNatFile i = plcTermFile (show i) (idNat id0 i)
        -- > id0 = foldNat {nat} succ zero
        id0 = mkIterApp () (tyInst () Plc.foldNat $ Plc.natTy) [Plc.succ, Plc.zero]

        idNat idN 0 = apply () idN $ metaIntegerToNat 10
        idNat idN n = idNat idN' (n - 1) where
            -- Intentionally not eta-expanding the call to @idN'@, so that it gets forced during
            -- evaluation, which causes @idN@ to get forced, which on the first iteration causes
            -- @id0@ to get forced, which gives us a sufficiently big AST.
            -- > idN' = id {nat -> nat} idN
            idN' = apply () (tyInst () (builtin () Id) $ Plc.TyFun () Plc.natTy Plc.natTy) idN

-- | Same as 'bunchOfIdNats' except uses the built-in @ifThenElse@.
bunchOfIfThenElseNats :: PlcFolderContents DefaultUni DefaultFun
bunchOfIfThenElseNats =
    FolderContents [treeFolderContents "IfThenElse" $ map ifThenElseNatFile [0 :: Int, 1.. 5]] where
        ifThenElseNatFile i = plcTermFile (show i) (ifThenElseNat id0 i) where
        -- > id0 = foldNat {nat} succ zero
        id0 = mkIterApp () (tyInst () Plc.foldNat $ Plc.natTy) [Plc.succ, Plc.zero]

        ifThenElseNat idN 0 = apply () idN $ metaIntegerToNat 10
        ifThenElseNat idN n = ifThenElseNat idN' (n - 1) where
            -- Eta-expanding @idN'@ so that all of the if-then-else-s don't get evaluated --
            -- only those that are on the actual execution path.
            -- > idN' = \(n : nat) -> ifThenElse {nat -> nat} ($(even n)) idN idN n
            idN'

                = etaExpand Plc.natTy
                $ mkIterApp () (tyInst () (builtin () IfThenElse) $ Plc.TyFun () Plc.natTy Plc.natTy)
                    [mkConstant () $ even n, idN, idN]

test_budget :: TestTree
test_budget
    = runTestNestedIn ["untyped-plutus-core", "test", "Evaluation", "Machines"]
    . testNested "Budget"
    $ concat
        [ folder defBuiltinsRuntime examples
        , folder defBuiltinsRuntime bunchOfFibs
        , folder (toBuiltinsRuntime mempty ()) bunchOfIdNats
        , folder defBuiltinsRuntime bunchOfIfThenElseNats
        ]
  where
    folder runtime =
        foldPlcFolderContents
            testNested
            (\name _ -> pure $ testGroup name [])
            (\name -> testBudget runtime name . erase)

testTallying :: TestName -> Term Name DefaultUni DefaultFun () -> TestNested
testTallying name term =
                       nestedGoldenVsText
    name
    (renderStrict $ layoutPretty defaultLayoutOptions {layoutPageWidth = AvailablePerLine maxBound 1.0} $
        prettyPlcReadableDef $ runCekNoEmit defBuiltinsRuntime Cek.tallying term)

test_tallying :: TestTree
test_tallying =
    runTestNestedIn ["untyped-plutus-core", "test", "Evaluation", "Machines"]
        .  testNested "Tallying"
        .  foldPlcFolderContents testNested
                                 (\name _ -> pure $ testGroup name [])
                                 (\name -> testTallying name . erase)
        $ examples <> bunchOfFibs
