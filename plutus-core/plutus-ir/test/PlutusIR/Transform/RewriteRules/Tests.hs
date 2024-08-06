module PlutusIR.Transform.RewriteRules.Tests where

import PlutusCore.Quote
import PlutusCore.Test hiding (ppCatch)
import PlutusIR.Compiler qualified as PIR
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.RewriteRules as RewriteRules
import PlutusPrelude

import Test.QuickCheck
import Test.Tasty

test_rewriteRules :: TestTree
test_rewriteRules =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "RewriteRules"] $
    fmap
      (goldenPir (runQuote . runTestPass (\tc -> rewritePassSC tc def)) pTerm)
      [ "equalsInt.pir" -- this tests that the function works on equalInteger
      , "divideInt.pir" -- this tests that the function excludes not commutative functions
      , "multiplyInt.pir" -- this tests that the function works on multiplyInteger
      , "let.pir" -- this tests that it works in the subterms
      , "unConstrConstrDataFst.pir"
      , "unConstrConstrDataSnd.pir"
      ]
      ++ fmap
        (goldenPirEvalTrace pTermAsProg)
        [ "unConstrConstrDataFst.pir.eval"
        ]
  where
    goldenPirEvalTrace = goldenPirM $ \ast -> ppCatch prettyPlcClassicSimple $ do
      -- we need traces to remain for checking the evaluation-order
      tplc <- asIfThrown $ compileWithOpts (set (PIR.ccOpts . PIR.coPreserveLogging) True) ast
      runUPlcLogs [void tplc]

prop_rewriteRules :: Property
prop_rewriteRules =
  withMaxSuccess numTestsForPassProp $ testPassProp runQuote $ \tc -> rewritePassSC tc def
