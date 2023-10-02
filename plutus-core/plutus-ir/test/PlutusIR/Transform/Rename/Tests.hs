module PlutusIR.Transform.Rename.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Pretty qualified as PLC
import PlutusCore.Quote
import PlutusCore.Rename qualified as PLC
import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.Rename ()

test_rename :: TestTree
test_rename = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "Rename" $
        map
            (goldenPir (PLC.AttachPrettyConfig debugConfig . runQuote . PLC.rename) pTerm)
            [ "allShadowedDataNonRec"
            , "allShadowedDataRec"
            , "paramShadowedDataNonRec"
            , "paramShadowedDataRec"
            ]
  where
    debugConfig = PLC.PrettyConfigClassic PLC.debugPrettyConfigName False

