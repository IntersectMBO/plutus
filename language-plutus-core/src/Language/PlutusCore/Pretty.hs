module Language.PlutusCore.Pretty
    (
    -- * Basic types and functions
      Doc
    , Pretty (..)
    , PrettyBy (..)
    , PrettyConfigIgnore (..)
    , PrettyConfigAttach (..)
    , docString
    , docText
    , prettyString
    , prettyText
    , prettyStringBy
    , prettyTextBy
    -- * Defaults
    , prettyPlcDef
    , prettyPlcDefString
    , prettyPlcDefText
    -- * Global configuration
    , PrettyConfigPlcOptions (..)
    , PrettyConfigPlcStrategy (..)
    , PrettyConfigPlc (..)
    , PrettyPlc
    , defPrettyConfigPlcOptions
    , defPrettyConfigPlcClassic
    , debugPrettyConfigPlcClassic
    , defPrettyConfigPlcReadable
    , debugPrettyConfigPlcReadable
    -- * Custom functions for PLC types.
    , prettyPlcClassicDef
    , prettyPlcClassicDebug
    , prettyPlcReadableDef
    , prettyPlcReadableDebug
    , prettyPlcCondensedErrorBy
    , prettyPlcCondensedErrorClassicString
    -- * Names
    , PrettyConfigName (..)
    , HasPrettyConfigName (..)
    , defPrettyConfigName
    , debugPrettyConfigName
    -- * Classic view
    , PrettyConfigClassic (..)
    , PrettyClassicBy
    -- * Readable view
    , RenderContext (..)
    , PrettyConfigReadable (..)
    , PrettyReadableBy
    , topPrettyConfigReadable
    , botPrettyConfigReadable
    ) where

import           Language.PlutusCore.Name            as Export
import           Language.PlutusCore.Pretty.Classic  as Export
import           Language.PlutusCore.Pretty.Plc      as Export
import           Language.PlutusCore.Pretty.Readable as Export
import           PlutusPrelude

import           Data.Text                           (Text)

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
