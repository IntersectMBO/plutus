module PlutusIR.Transform.Rename.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Pretty qualified as PLC
import PlutusCore.Quote
import PlutusIR.Parser
import PlutusIR.Pass
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.Rename ()
import Test.Tasty.QuickCheck

test_rename :: TestTree
test_rename =
    runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "Rename"] $
        map
            (goldenPir
             (PLC.AttachPrettyConfig debugConfig . runQuote . runTestPass (const renamePass)) pTerm)
            [ "allShadowedDataNonRec"
            , "allShadowedDataRec"
            , "paramShadowedDataNonRec"
            , "paramShadowedDataRec"
            ]
  where
    debugConfig = PLC.PrettyConfigClassic PLC.debugPrettyConfigName False

prop_rename :: Property
prop_rename =
  withMaxSuccess numTestsForPassProp $ testPassProp runQuote (const renamePass)
