module PlutusIR.Transform.NonStrict.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Quote
import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.NonStrict qualified as NonStrict
import PlutusIR.Transform.Rename ()

test_nonStrict :: TestTree
test_nonStrict = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "NonStrict" $
        map
            (goldenPir (runQuote . NonStrict.compileNonStrictBindings False) pTerm)
            [ "nonStrict1"
            ]

