module PlutusIR.Transform.NonStrict.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Quote
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.NonStrict qualified as NonStrict
import PlutusIR.Transform.Rename ()
import Test.QuickCheck

test_nonStrict :: TestTree
test_nonStrict = runTestNestedIn ["plutus-ir", "test", "PlutusIR", "Transform"] $
    testNested "NonStrict" $
        map
            (goldenPir (runQuote . runTestPass
                        (\tc -> NonStrict.compileNonStrictBindingsPassSC tc False)) pTerm)
            [ "nonStrict1"
            ]

prop_nonStrict :: Bool -> Property
prop_nonStrict useUnit = withMaxSuccess (2 * numTestsForPassProp) $
  testPassProp runQuote $ \tc -> NonStrict.compileNonStrictBindingsPassSC tc useUnit
