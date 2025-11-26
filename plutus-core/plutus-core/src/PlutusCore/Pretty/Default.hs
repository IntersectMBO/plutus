module PlutusCore.Pretty.Default
  ( prettyPlc
  , displayPlc
  , prettyPlcSimple
  , displayPlcSimple
  , displayPlcCondensedErrorClassic
  ) where

import PlutusPrelude

import PlutusCore.Pretty.Plc

-- | Pretty-print a value in the default mode using the classic view.
prettyPlc :: PrettyPlc a => a -> Doc ann
prettyPlc = prettyPlcClassic

-- | Render a value to 'String' in the default mode using the classic view.
displayPlc :: (PrettyPlc a, Render str) => a -> str
displayPlc = render . prettyPlcClassic

-- | Pretty-print a value in the debug mode using the classic view.
prettyPlcSimple :: PrettyPlc a => a -> Doc ann
prettyPlcSimple = prettyPlcClassicSimple

-- | Render a value to 'String' in the debug mode using the classic view.
displayPlcSimple :: (PrettyPlc a, Render str) => a -> str
displayPlcSimple = render . prettyPlcClassicSimple

-- | Render an error to 'String' in the condensed manner using the classic view.
displayPlcCondensedErrorClassic :: (PrettyPlc a, Render str) => a -> str
displayPlcCondensedErrorClassic =
  render . prettyPlcCondensedErrorBy prettyConfigPlcClassic
