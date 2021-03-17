module PlutusCore.Pretty.Default
    ( prettyPlcDef
    , displayPlcDef
    , displayPlcCondensedErrorClassic
    ) where

import           PlutusPrelude

import           PlutusCore.Pretty.Plc

-- | Pretty-print a value in the default mode using the classic view.
prettyPlcDef :: PrettyPlc a => a -> Doc ann
prettyPlcDef = prettyPlcClassicDef

-- | Render a value to 'String' in the default mode using the classic view.
displayPlcDef :: (PrettyPlc a, Render str) => a -> str
displayPlcDef = render . prettyPlcClassicDef

-- | Render an error to 'String' in the condensed manner using the classic view.
displayPlcCondensedErrorClassic :: (PrettyPlc a, Render str) => a -> str
displayPlcCondensedErrorClassic =
    render . prettyPlcCondensedErrorBy defPrettyConfigPlcClassic
