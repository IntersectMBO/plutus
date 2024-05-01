module PlutusIR.Compiler.Datatype.Tests where

import PlutusIR.Parser (pTerm)
import PlutusIR.Test

import Test.Tasty
import Test.Tasty.Extras

test_datatypes :: TestTree
test_datatypes =
    runTestNestedM ["plutus-ir", "test", "PlutusIR", "Compiler", "Datatype"] $ do
        goldenPlcFromPir pTermAsProg "maybe"
        goldenPlcFromPir pTermAsProg "listMatch"
        goldenPlcFromPir pTermAsProg "idleAll"
        goldenPlcFromPir pTermAsProg "some"
        goldenEvalPir pTermAsProg "listMatchEval"
        goldenTypeFromPir topSrcSpan pTerm "dataEscape"
        testNestedM "scott" $ do
            goldenPlcFromPirScott pTermAsProg "maybe"
            goldenPlcFromPirScott pTermAsProg "listMatch"
