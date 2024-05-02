{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusIR.Transform.StrictLetRec.Tests where

import PlutusPrelude

import PlutusCore.Default (someValue)
import PlutusIR.Compiler (Provenance (Original))
import PlutusIR.Compiler.Let (LetKind (RecTerms), compileLetsPassSC)
import PlutusIR.MkPir (constant)
import PlutusIR.Parser (pTerm)
import PlutusIR.Pass.Test (runTestPass)
import PlutusIR.Test (goldenPir)
import PlutusIR.Transform.StrictLetRec.Tests.Lib (evaluatePirFromFile, runCompilationM)
import System.FilePath.Posix (joinPath, (</>))
import Test.Tasty (TestTree)
import Test.Tasty.Extras (runTestNestedIn, testNested)
import Test.Tasty.HUnit (testCase, (@?=))
import UntypedPlutusCore.Evaluation.Machine.Cek (EvaluationResult (..))

path :: [FilePath]
path = ["plutus-ir", "test", "PlutusIR", "Transform"]

test_letRec :: TestTree
test_letRec = runTestNestedIn path do
  testNested
    "StrictLetRec"
    [ goldenPir
        (runCompilationM . runTestPass (\tcConfig -> compileLetsPassSC tcConfig RecTerms))
        (const (Original ()) <<$>> pTerm)
        "strictLetRec"
    , pure $ testCase "traces" do
        (result, traces) <-
          evaluatePirFromFile $ joinPath path </> "StrictLetRec" </> "strictLetRec"
        case result of
          EvaluationFailure ->
            fail $ "Evaluation failed, available traces: " <> show traces
          EvaluationSuccess term -> do
            term @?= constant () (someValue (1 :: Integer))
            traces @?= ["hello"]
    ]
