-- | The global pretty-printing config used to pretty-print everything in the PLC world.
-- This module also defines custom pretty-printing functions for PLC types as a convenience.

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Pretty.Plc
    (
    -- * Global configuration
      PrettyConfigPlcOptions (..)
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
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty.Classic
import           Language.PlutusCore.Pretty.Readable
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | Options for pretty-printing PLC entities.
newtype PrettyConfigPlcOptions = PrettyConfigPlcOptions
    { _pcpoCondensedErrors :: Bool
    }

-- | Strategy for pretty-printing PLC entities.
data PrettyConfigPlcStrategy
    = PrettyConfigPlcClassic (PrettyConfigClassic PrettyConfigName)
    | PrettyConfigPlcReadable (PrettyConfigReadable PrettyConfigName)

-- | Global configuration used for pretty-printing PLC entities.
data PrettyConfigPlc = PrettyConfigPlc
    { _pcpOptions  :: PrettyConfigPlcOptions
    , _pcpStrategy :: PrettyConfigPlcStrategy
    }

-- | The "pretty-printable PLC entity" constraint.
type PrettyPlc = PrettyBy PrettyConfigPlc

-- | A constraint that allows to derive @PrettyBy PrettyConfigPlc@ instances, see below.
type DefaultPrettyPlcStrategy a =
       ( PrettyBy (PrettyConfigClassic PrettyConfigName) a
       , PrettyBy (PrettyConfigReadable PrettyConfigName) a
       )

instance HasPrettyConfigName PrettyConfigPlcStrategy where
    toPrettyConfigName (PrettyConfigPlcClassic configClassic)   = toPrettyConfigName configClassic
    toPrettyConfigName (PrettyConfigPlcReadable configReadable) = toPrettyConfigName configReadable

instance HasPrettyConfigName PrettyConfigPlc where
    toPrettyConfigName = toPrettyConfigName . _pcpStrategy

instance DefaultPrettyPlcStrategy a => DefaultPrettyBy PrettyConfigPlcStrategy a where
    defaultPrettyBy (PrettyConfigPlcClassic configClassic)   = prettyBy configClassic
    defaultPrettyBy (PrettyConfigPlcReadable configReadable) = prettyBy configReadable

instance DefaultPrettyPlcStrategy a => DefaultPrettyBy PrettyConfigPlc a where
    defaultPrettyBy = defaultPrettyBy . _pcpStrategy

instance PrettyBy PrettyConfigPlc (Kind a)
instance PrettyBy PrettyConfigPlc (Constant a)
instance DefaultPrettyPlcStrategy (Type tyname a) =>
    PrettyBy PrettyConfigPlc (Type tyname a)
instance DefaultPrettyPlcStrategy (Term tyname name a) =>
    PrettyBy PrettyConfigPlc (Term tyname name a)
instance DefaultPrettyPlcStrategy (Program tyname name a) =>
    PrettyBy PrettyConfigPlc (Program tyname name a)

instance PrettyBy PrettyConfigPlc BuiltinName where
    prettyBy _ = pretty

-- | The 'PrettyConfigPlcOptions' used by default:
-- print errors in full.
defPrettyConfigPlcOptions :: PrettyConfigPlcOptions
defPrettyConfigPlcOptions = PrettyConfigPlcOptions False

-- | The 'PrettyConfigPlc' used by default:
-- use the classic view and print neither 'Unique's, nor name attachments.
defPrettyConfigPlcClassic :: PrettyConfigPlcOptions -> PrettyConfigPlc
defPrettyConfigPlcClassic opts =
    PrettyConfigPlc opts . PrettyConfigPlcClassic $ PrettyConfigClassic defPrettyConfigName

-- | The 'PrettyConfigPlc' used for debugging:
-- use the classic view and print 'Unique's, but not name attachments.
debugPrettyConfigPlcClassic :: PrettyConfigPlcOptions -> PrettyConfigPlc
debugPrettyConfigPlcClassic opts =
    PrettyConfigPlc opts . PrettyConfigPlcClassic $ PrettyConfigClassic debugPrettyConfigName

-- | The 'PrettyConfigPlc' used by default and for readability:
-- use the refined view and print neither 'Unique's, nor name attachments.
defPrettyConfigPlcReadable :: PrettyConfigPlcOptions -> PrettyConfigPlc
defPrettyConfigPlcReadable opts =
    PrettyConfigPlc opts . PrettyConfigPlcReadable $ topPrettyConfigReadable defPrettyConfigName

-- | The 'PrettyConfigPlc' used for debugging and readability:
-- use the refined view and print 'Unique's, but not name attachments.
debugPrettyConfigPlcReadable :: PrettyConfigPlcOptions -> PrettyConfigPlc
debugPrettyConfigPlcReadable opts =
    PrettyConfigPlc opts . PrettyConfigPlcReadable $ topPrettyConfigReadable debugPrettyConfigName

-- | Pretty-print a value in the default mode using the classic view.
prettyPlcClassicDef :: PrettyPlc a => a -> Doc ann
prettyPlcClassicDef = prettyBy $ defPrettyConfigPlcClassic defPrettyConfigPlcOptions

-- | Pretty-print a value in the debug mode using the classic view.
prettyPlcClassicDebug :: PrettyPlc a => a -> Doc ann
prettyPlcClassicDebug = prettyBy $ debugPrettyConfigPlcClassic defPrettyConfigPlcOptions

-- | Pretty-print a value in the default mode using the readable view.
prettyPlcReadableDef :: PrettyPlc a => a -> Doc ann
prettyPlcReadableDef = prettyBy $ defPrettyConfigPlcReadable defPrettyConfigPlcOptions

-- | Pretty-print a value in the debug mode using the readable view.
prettyPlcReadableDebug :: PrettyPlc a => a -> Doc ann
prettyPlcReadableDebug = prettyBy $ debugPrettyConfigPlcReadable defPrettyConfigPlcOptions

prettyPlcCondensedErrorBy
    :: PrettyPlc a => (PrettyConfigPlcOptions -> PrettyConfigPlc) -> a -> Doc ann
prettyPlcCondensedErrorBy toConfig = prettyBy (toConfig $ PrettyConfigPlcOptions True)
