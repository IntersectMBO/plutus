-- There is really no way to avoid these being orphans without a cycle
-- between the pretty printing and AST modules.
{-# OPTIONS_GHC -Wno-orphans -Wno-simplifiable-class-constraints #-}

{-# LANGUAGE UndecidableInstances #-}

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
    ) where

import           Language.PlutusCore.Name            as Export
import           Language.PlutusCore.Pretty.Classic  as Export
import           Language.PlutusCore.Pretty.Plc      as Export
import           Language.PlutusCore.Pretty.Readable as Export
import           Language.PlutusCore.Type
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

{- Note [Default pretty instances for PLC]
While the flexible pretty-printing infrastructure is useful when you want it,
it's helpful to have an implementation of the default Pretty typeclass that
does the default thing.
-}
instance Pretty (Kind a) where
    pretty = prettyClassicDef
instance Pretty (Constant a) where
    pretty = prettyClassicDef
instance Pretty (Builtin a) where
    pretty = prettyClassicDef
instance PrettyClassic (Type tyname a) => Pretty (Type tyname a) where
    pretty = prettyClassicDef
instance PrettyClassic (Term tyname name a) => Pretty (Term tyname name a) where
    pretty = prettyClassicDef
instance PrettyClassic (Program tyname name a) => Pretty (Program tyname name a) where
    pretty = prettyClassicDef
