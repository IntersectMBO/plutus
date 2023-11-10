module PlutusIR.Transform.RewriteRules.Tests where

import PlutusCore.Quote
import PlutusCore.Test hiding (ppCatch)
import PlutusIR.Compiler qualified as PIR
import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.RewriteRules as RewriteRules
import PlutusPrelude

import Test.Tasty

test_RewriteRules :: TestTree
test_RewriteRules = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "RewriteRules" $
    (fmap
        (goldenPirDoc (prettyPlcClassicDebug . runQuote . RewriteRules.rewriteWith def)  pTerm)
        [ "equalsInt.pir" -- this tests that the function works on equalInteger
        , "divideInt.pir" -- this tests that the function excludes not commutative functions
        , "multiplyInt.pir" -- this tests that the function works on multiplyInteger
        , "let.pir" -- this tests that it works in the subterms
        , "unConstrConstrDataFst.pir"
        , "unConstrConstrDataSnd.pir"
        ]
    )
    ++
    (fmap
        (goldenPirEvalTrace pTermAsProg)
        [ "unConstrConstrDataFst.pir.eval"
        ]
    )

  where
    goldenPirEvalTrace = goldenPirM $ \ast -> ppCatch $ do
          -- we need traces to remain for checking the evaluation-order
          tplc <- asIfThrown $ compileWithOpts ( set (PIR.ccOpts . PIR.coPreserveLogging) True) ast
          runUPlcLogs [void tplc]
