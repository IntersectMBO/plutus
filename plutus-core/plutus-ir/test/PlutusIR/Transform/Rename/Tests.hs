module PlutusIR.Transform.Rename.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Pretty qualified as PLC
import PlutusCore.Quote
import PlutusCore.Rename qualified as PLC
import PlutusIR.Parser
import PlutusIR.Properties.Typecheck
import PlutusIR.Test
import PlutusIR.Transform.Rename ()
import Test.Tasty.QuickCheck

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

-- | Check that a term typechecks after a `PlutusIR.Transform.Rename.rename` pass.
prop_TypecheckRename :: Property
prop_TypecheckRename =
  withMaxSuccess 5000 (nonPureTypecheckProp PLC.rename)
