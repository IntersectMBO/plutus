module Language.PlutusCore.Pretty
    (
    -- * Basic types and functions
      Doc
    , Pretty (..)
    , PrettyBy (..)
    , IgnorePrettyConfig (..)
    , AttachPrettyConfig (..)
    , Render (..)
    , display
    , displayBy
    -- * Defaults
    , prettyPlcDef
    , displayPlcDef
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
    , displayPlcCondensedErrorClassic
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
    , ShowKinds (..)
    , PrettyConfigReadable (..)
    , PrettyReadableBy
    , PrettyReadable
    , topPrettyConfigReadable
    , botPrettyConfigReadable
    -- * Utils
    , prettyBytes
    , PrettyConst (..)
    ) where

import           Language.PlutusCore.Pretty.Classic
import           Language.PlutusCore.Pretty.ConfigName
import           Language.PlutusCore.Pretty.Default
import           Language.PlutusCore.Pretty.Plc
import           Language.PlutusCore.Pretty.PrettyConst
import           Language.PlutusCore.Pretty.Readable
import           Language.PlutusCore.Pretty.Utils

import           Text.Pretty
import           Text.PrettyBy
