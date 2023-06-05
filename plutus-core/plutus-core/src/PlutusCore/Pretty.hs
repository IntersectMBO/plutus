module PlutusCore.Pretty
    (
    -- * Basic types and functions
      Doc
    , Pretty (..)
    , PrettyBy (..)
    , IgnorePrettyConfig (..)
    , AttachPrettyConfig (..)
    , Render (..)
    , PrettyParens
    , display
    , displayBy
    , prettyParens
    -- * Defaults
    , prettyPlcDef
    , displayPlcDef
    , prettyPlcDebug
    , displayPlcDebug
    -- * Global configuration
    , CondensedErrors (..)
    , DefaultPrettyPlcStrategy
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
    , consAnnIf
    , prettyClassicDef
    , prettyClassicDebug
    -- * Readable view
    , ShowKinds (..)
    , PrettyConfigReadable (..)
    , pcrConfigName
    , pcrRenderContext
    , pcrShowKinds
    , PrettyReadableBy
    , PrettyReadable
    , AsReadable (..)
    , topPrettyConfigReadable
    , botPrettyConfigReadable
    , binderFixity
    , arrowFixity
    , arrowPrettyM
    , iterTyForallPrettyM
    , iterLamAbsPrettyM
    , iterTyAbsPrettyM
    , iterAppPrettyM
    -- * Utils
    , prettyBytes
    , ConstConfig (..)
    , PrettyConst
    , PrettyUni
    , ThrowableBuiltins
    , prettyConst
    , displayConst
    , module Export
    ) where

import PlutusCore.Pretty.Classic
import PlutusCore.Pretty.ConfigName
import PlutusCore.Pretty.Default
import PlutusCore.Pretty.Extra ()
import PlutusCore.Pretty.Plc
import PlutusCore.Pretty.PrettyConst
import PlutusCore.Pretty.Readable
import PlutusCore.Pretty.Utils

import Text.Pretty
import Text.PrettyBy
import Text.PrettyBy.Fixity as Export
