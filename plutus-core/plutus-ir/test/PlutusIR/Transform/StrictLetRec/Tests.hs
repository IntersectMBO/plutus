{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusIR.Transform.StrictLetRec.Tests where

import PlutusPrelude

import PlutusCore.Default (someValue)
import PlutusCore.MkPlc (constant)
import PlutusCore.Pretty (AsReadable (..))
import PlutusCore.Quote (runQuoteT)
import PlutusCore.Version (latestVersion)
import PlutusIR.Compiler.Let (LetKind (RecTerms), compileLetsPassSC)
import PlutusIR.Compiler.Provenance (noProvenance)
import PlutusIR.Core qualified as PIR
import PlutusIR.Parser (pTerm)
import PlutusIR.Pass.Test (runTestPass)
import PlutusIR.Test (goldenPirM)
import PlutusIR.Transform.StrictLetRec.Tests.Lib
  ( compilePirProgramOrFail
  , compileTplcProgramOrFail
  , defaultCompilationCtx
  , evalPirProgramWithTracesOrFail
  , pirTermAsProgram
  , pirTermFromFile
  )
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (EvaluationResult (..))

import Control.Monad.Except (runExcept)
import Control.Monad.Reader (runReaderT)
import System.FilePath.Posix (joinPath, (</>))
import Test.Tasty (TestTree)
import Test.Tasty.Extras (embed, runTestNested, testNested)
import Test.Tasty.HUnit (testCase, (@?=))

path :: [FilePath]
path = ["plutus-ir", "test", "PlutusIR", "Transform"]

test_letRec :: TestTree
test_letRec =
  runTestNested path . pure $
    testNested
      "StrictLetRec"
      [ let
          runCompilationM m = either (fail . show) pure do
            ctx <- defaultCompilationCtx
            runExcept . runQuoteT $ runReaderT m ctx
          dumpUplc pirTermBefore = do
            pirTermAfter <-
              runCompilationM $
                fmap void . runTestPass (`compileLetsPassSC` RecTerms) $
                  noProvenance <$ pirTermBefore
            tplcProg <- compilePirProgramOrFail $ PIR.Program () latestVersion pirTermAfter
            uplcProg <- compileTplcProgramOrFail tplcProg
            pure . AsReadable $ UPLC._progTerm uplcProg
         in
          goldenPirM dumpUplc pTerm "strictLetRec"
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
