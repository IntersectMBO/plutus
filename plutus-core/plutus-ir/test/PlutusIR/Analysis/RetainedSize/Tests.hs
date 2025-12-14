module PlutusIR.Analysis.RetainedSize.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Name.Unique
import PlutusCore.Pretty qualified as PLC
import PlutusCore.Quote
import PlutusCore.Rename qualified as PLC
import PlutusIR.Analysis.RetainedSize qualified as RetainedSize
import PlutusIR.Parser
import PlutusIR.Test
import PlutusPrelude

test_retainedSize :: TestTree
test_retainedSize =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Analysis", "RetainedSize"] $
    map
      (goldenPirUnique renameAndAnnotate pTerm)
      [ "typeLet"
      , "termLet"
      , "strictLet"
      , "nonstrictLet"
      , -- @Maybe@ is referenced, so it retains all of the data type.
        "datatypeLiveType"
      , -- @Nothing@ is referenced, so it retains all of the data type.
        "datatypeLiveConstr"
      , -- @match_Maybe@ is referenced, so it retains all of the data type.
        "datatypeLiveDestr"
      , "datatypeDead"
      , "singleBinding"
      , "builtinBinding"
      , "etaBuiltinBinding"
      , "etaBuiltinBindingUsed"
      , "nestedBindings"
      , "nestedBindingsIndirect"
      , "recBindingSimple"
      , "recBindingComplex"
      ]
  where
    displayAnnsConfig = PLC.PrettyConfigClassic PLC.prettyConfigNameSimple True
    renameAndAnnotate =
      PLC.AttachPrettyConfig displayAnnsConfig
        . RetainedSize.annotateWithRetainedSize def
        . runQuote
        . PLC.rename
