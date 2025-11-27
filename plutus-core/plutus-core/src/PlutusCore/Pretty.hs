module PlutusCore.Pretty
  ( -- * Basic types and functions
    Doc
  , Pretty (..)
  , PrettyBy (..)
  , IgnorePrettyConfig (..)
  , AttachPrettyConfig (..)
  , Render (..)
  , PrettyParens
  , display
  , displayBy
  , juxtRenderContext

    -- * Defaults
  , prettyPlc
  , displayPlc
  , prettyPlcSimple
  , displayPlcSimple

    -- * Global configuration
  , CondensedErrors (..)
  , DefaultPrettyPlcStrategy
  , PrettyConfigPlcOptions (..)
  , PrettyConfigPlcStrategy (..)
  , PrettyConfigPlc (..)
  , PrettyPlc
  , prettyConfigPlcOptions
  , prettyConfigPlcClassic
  , prettyConfigPlcClassicSimple
  , prettyConfigPlcReadable
  , prettyConfigPlcReadableSimple

    -- * Custom functions for PLC types.
  , prettyPlcClassic
  , prettyPlcClassicSimple
  , prettyPlcReadable
  , prettyPlcReadableSimple
  , prettyPlcCondensedErrorBy
  , displayPlcCondensedErrorClassic

    -- * Names
  , PrettyConfigName (..)
  , HasPrettyConfigName (..)
  , prettyConfigName
  , prettyConfigNameSimple

    -- * Classic view
  , PrettyConfigClassic (..)
  , PrettyClassicBy
  , PrettyClassic
  , consAnnIf
  , prettyClassic
  , prettyClassicSimple

    -- * Readable view
  , ShowKinds (..)
  , PrettyConfigReadable (..)
  , prettyReadable
  , prettyReadableSimple
  , pcrConfigName
  , pcrRenderContext
  , pcrShowKinds
  , PrettyReadableBy
  , PrettyReadable
  , AsReadable (..)
  , Parened (..)
  , inBraces
  , topPrettyConfigReadable
  , botPrettyConfigReadable
  , binderFixity
  , arrowFixity
  , iterTyForallPrettyM
  , iterLamAbsPrettyM
  , iterTyAbsPrettyM
  , iterArrowPrettyM
  , iterAppDocM
  , iterInterAppPrettyM
  , iterAppPrettyM

    -- * Utils
  , prettyBytes
  , ConstConfig (..)
  , PrettyConst
  , PrettyUni
  , ThrowableBuiltins
  , prettyConst
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
