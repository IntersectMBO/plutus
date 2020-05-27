module Language.PlutusCore.Pretty.Default
    ( prettyPlcDef
    , prettyPlcDefString
    , prettyPlcDefText
    , prettyPlcCondensedErrorClassicString
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Pretty.Plc

import           Data.Text                      (Text)

-- | Pretty-print a value in the default mode using the classic view.
prettyPlcDef :: PrettyPlc a => a -> Doc ann
prettyPlcDef = prettyPlcClassicDef

-- | Render a value to 'String' in the default mode using the classic view.
prettyPlcDefString :: PrettyPlc a => a -> String
prettyPlcDefString = docString . prettyPlcClassicDef

-- | Render a value to 'Text' in the default mode using the classic view.
prettyPlcDefText :: PrettyPlc a => a -> Text
prettyPlcDefText = docText . prettyPlcClassicDef

-- | Render an error to 'String' in the condensed manner using the classic view.
prettyPlcCondensedErrorClassicString :: PrettyPlc a => a -> String
prettyPlcCondensedErrorClassicString =
    docString . prettyPlcCondensedErrorBy defPrettyConfigPlcClassic
