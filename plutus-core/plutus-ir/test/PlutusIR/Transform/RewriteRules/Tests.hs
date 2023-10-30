module PlutusIR.Transform.RewriteRules.Tests where

import PlutusCore.Quote
import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.RewriteRules as RewriteRules

import Data.Default.Class
import Test.Tasty
import Test.Tasty.Extras

test_RewriteRules :: TestTree
test_RewriteRules = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "RewriteRules" $
    fmap
        (goldenPir (runQuote . RewriteRules.rewriteWith def)  pTerm)
        [ "equalsInt" -- this tests that the function works on equalInteger
        , "divideInt" -- this tests that the function excludes not commutative functions
        , "multiplyInt" -- this tests that the function works on multiplyInteger
        , "let" -- this tests that it works in the subterms
        ]
