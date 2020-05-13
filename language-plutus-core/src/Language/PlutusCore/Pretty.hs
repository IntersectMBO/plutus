
module Language.PlutusCore.Pretty
    (
    -- * Basic types and functions
      Doc
    , Pretty (..)
    , PrettyM (..)
    , IgnorePrettyConfig (..)
    , AttachPrettyConfig (..)
    , docString
    , docText
    , prettyString
    , prettyText
    , prettyDefBy
    -- * Defaults
    , prettyPlcDef
    , prettyPlcDefString
    , prettyPlcDefText
    -- * Global configuration
    , CondensedErrors (..)
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
    , PrettyClassic
    , prettyClassicDef
    , prettyClassicDebug
    -- * Readable view
    , RenderContext (..)
    , ShowKinds (..)
    , PrettyConfigReadable (..)
    , PrettyReadableBy
    , PrettyReadable
    , topPrettyConfigReadable
    , botPrettyConfigReadable
    -- * Utils
    , prettyBytes
    ) where

import           Language.PlutusCore.Pretty.Classic
import           Language.PlutusCore.Pretty.ConfigName
import           Language.PlutusCore.Pretty.Default
import           Language.PlutusCore.Pretty.Plc
import           Language.PlutusCore.Pretty.PrettyM
import           Language.PlutusCore.Pretty.Readable
import           Language.PlutusCore.Pretty.Utils

import           Data.Text.Prettyprint.Doc
