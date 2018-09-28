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
      PrettyConfigPlc (..)
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
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty.Classic
import           Language.PlutusCore.Pretty.Readable
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | Global configuration used for pretty-printing PLC entities.
data PrettyConfigPlc
    = PrettyConfigPlcClassic (PrettyConfigClassic PrettyConfigName)
    | PrettyConfigPlcReadable (PrettyConfigReadable PrettyConfigName)

-- | The "pretty-printable PLC entity" constraint.
type PrettyPlc = PrettyBy PrettyConfigPlc

-- | A constraint that allows to derive @PrettyBy PrettyConfigPlc@ instances, see below.
type DefaultPrettyPlc a =
       ( PrettyBy (PrettyConfigClassic PrettyConfigName) a
       , PrettyBy (PrettyConfigReadable PrettyConfigName) a
       )

instance HasPrettyConfigName PrettyConfigPlc where
    toPrettyConfigName (PrettyConfigPlcClassic configClassic)   = toPrettyConfigName configClassic
    toPrettyConfigName (PrettyConfigPlcReadable configReadable) = toPrettyConfigName configReadable

instance DefaultPrettyPlc a => DefaultPrettyBy PrettyConfigPlc a where
    defaultPrettyBy (PrettyConfigPlcClassic configClassic)   = prettyBy configClassic
    defaultPrettyBy (PrettyConfigPlcReadable configReadable) = prettyBy configReadable

instance PrettyBy PrettyConfigPlc (Kind a)
instance PrettyBy PrettyConfigPlc (Constant a)
instance DefaultPrettyPlc (Type tyname a) => PrettyBy PrettyConfigPlc (Type tyname a)
instance DefaultPrettyPlc (Term tyname name a) => PrettyBy PrettyConfigPlc (Term tyname name a)
instance DefaultPrettyPlc (Program tyname name a) => PrettyBy PrettyConfigPlc (Program tyname name a)

instance PrettyBy PrettyConfigPlc BuiltinName where
    prettyBy _ = pretty

-- | The 'PrettyConfigPlc' used by default:
-- use the classic view and print neither 'Unique's, nor name attachments.
defPrettyConfigPlcClassic :: PrettyConfigPlc
defPrettyConfigPlcClassic = PrettyConfigPlcClassic $ PrettyConfigClassic defPrettyConfigName

-- | The 'PrettyConfigPlc' used for debugging:
-- use the classic view and print 'Unique's, but not name attachments.
debugPrettyConfigPlcClassic :: PrettyConfigPlc
debugPrettyConfigPlcClassic = PrettyConfigPlcClassic $ PrettyConfigClassic debugPrettyConfigName

-- | The 'PrettyConfigPlc' used by default and for readability:
-- use the refined view and print neither 'Unique's, nor name attachments.
defPrettyConfigPlcReadable :: PrettyConfigPlc
defPrettyConfigPlcReadable = PrettyConfigPlcReadable $ topPrettyConfigReadable defPrettyConfigName

-- | The 'PrettyConfigPlc' used for debugging and readability:
-- use the refined view and print 'Unique's, but not name attachments.
debugPrettyConfigPlcReadable :: PrettyConfigPlc
debugPrettyConfigPlcReadable = PrettyConfigPlcReadable $ topPrettyConfigReadable debugPrettyConfigName

prettyPlcClassicBy :: PrettyPlc a => PrettyConfigClassic PrettyConfigName -> a -> Doc ann
prettyPlcClassicBy = prettyBy . PrettyConfigPlcClassic

prettyPlcClassicDefBy :: PrettyPlc a => PrettyConfigName -> a -> Doc ann
prettyPlcClassicDefBy = prettyPlcClassicBy . PrettyConfigClassic

prettyPlcClassicDef :: PrettyPlc a => a -> Doc ann
prettyPlcClassicDef = prettyBy defPrettyConfigPlcClassic

prettyPlcClassicDebug :: PrettyPlc a => a -> Doc ann
prettyPlcClassicDebug = prettyBy debugPrettyConfigPlcClassic

prettyPlcReadableBy :: PrettyPlc a => PrettyConfigReadable PrettyConfigName -> a -> Doc ann
prettyPlcReadableBy = prettyBy . PrettyConfigPlcReadable

prettyPlcReadableDefBy :: PrettyPlc a => PrettyConfigName -> a -> Doc ann
prettyPlcReadableDefBy = prettyPlcReadableBy . topPrettyConfigReadable

prettyPlcReadableDef :: PrettyPlc a => a -> Doc ann
prettyPlcReadableDef = prettyBy defPrettyConfigPlcReadable

prettyPlcReadableDebug :: PrettyPlc a => a -> Doc ann
prettyPlcReadableDebug = prettyBy debugPrettyConfigPlcReadable
