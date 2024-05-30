{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusIR.Transform.StrictLetRec.Tests where

import PlutusPrelude

import Control.Monad.Except (runExcept)
import Control.Monad.Reader (runReaderT)
import PlutusCore.Default (someValue)
import PlutusCore.MkPlc (constant)
import PlutusCore.Quote (runQuoteT)
import PlutusIR.Compiler.Let (LetKind (RecTerms), compileLetsPassSC)
import PlutusIR.Compiler.Provenance (noProvenance)
import PlutusIR.Parser (pTerm)
import PlutusIR.Pass.Test (runTestPass)
import PlutusIR.Test (goldenPirM)
import PlutusIR.Transform.StrictLetRec.Tests.Lib (defaultCompilationCtx,
                                                  evalPirProgramWithTracesOrFail, pirTermAsProgram,
                                                  pirTermFromFile)
import System.FilePath.Posix (joinPath, (</>))
import Test.Tasty (TestTree)
import Test.Tasty.Extras (embed, runTestNested, testNested)
import Test.Tasty.HUnit (testCase, (@?=))
import UntypedPlutusCore.Evaluation.Machine.Cek (EvaluationResult (..))

path :: [FilePath]
path = ["plutus-ir", "test", "PlutusIR", "Transform"]

test_letRec :: TestTree
test_letRec = runTestNested path . pure $ testNested "StrictLetRec"
    [ let
        runCompilationM m = either (fail . show) pure do
          ctx <- defaultCompilationCtx
          runExcept . runQuoteT $ runReaderT m ctx
       in
        goldenPirM
          (runCompilationM . runTestPass (`compileLetsPassSC` RecTerms))
          (const noProvenance <<$>> pTerm)
          "strictLetRec"
    , embed $ testCase "traces" do
        (result, traces) <- do
          pirTerm <- pirTermFromFile (joinPath path </> "StrictLetRec" </> "strictLetRec")
          evalPirProgramWithTracesOrFail (pirTermAsProgram (void pirTerm))
        case result of
          EvaluationFailure ->
            fail $ "Evaluation failed, available traces: " <> show traces
          EvaluationSuccess term -> do
            term @?= constant () (someValue (1 :: Integer))
            traces @?= ["hello"]
    ]
