module Language.PlutusCore.Pretty
    (
    -- * Basic types and functions
      Pretty (..)
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
    , PrettyConfigPlc (..)
    , PrettyPlc
    , defPrettyConfigPlcClassic
    , debugPrettyConfigPlcClassic
    , defPrettyConfigPlcReadable
    , debugPrettyConfigPlcReadable
    -- * Custom functions for PLC types.
    , prettyPlcClassicBy
    , prettyPlcClassicDefBy
    , prettyPlcClassicDef
    , prettyPlcClassicDebug
    , prettyPlcReadableBy
    , prettyPlcReadableDefBy
    , prettyPlcReadableDef
    , prettyPlcReadableDebug
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

prettyPlcDef :: PrettyPlc a => a -> Doc ann
prettyPlcDef = prettyPlcClassicDef

prettyPlcDefString :: PrettyPlc a => a -> String
prettyPlcDefString = docString . prettyPlcClassicDef

prettyPlcDefText :: PrettyPlc a => a -> Text
prettyPlcDefText = docText . prettyPlcClassicDef
