{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-| The global pretty-printing config used to pretty-print everything in the PLC world.
This module also defines custom pretty-printing functions for PLC types as a convenience. -}
module PlutusCore.Pretty.Plc
  ( -- * Global configuration
    CondensedErrors (..)
  , PrettyConfigPlcOptions (..)
  , PrettyConfigPlcStrategy (..)
  , PrettyConfigPlc (..)
  , PrettyPlc
  , DefaultPrettyPlcStrategy
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
  ) where

import PlutusPrelude

import PlutusCore.Pretty.Classic
import PlutusCore.Pretty.ConfigName
import PlutusCore.Pretty.Readable

-- | Whether to pretty-print PLC errors in full or with some information omitted.
data CondensedErrors
  = CondensedErrorsYes
  | CondensedErrorsNo
  deriving stock (Show, Eq)

-- | Options for pretty-printing PLC entities.
newtype PrettyConfigPlcOptions = PrettyConfigPlcOptions
  { _pcpoCondensedErrors :: CondensedErrors
  }
  deriving stock (Show)

-- | Strategy for pretty-printing PLC entities.
data PrettyConfigPlcStrategy
  = PrettyConfigPlcClassic (PrettyConfigClassic PrettyConfigName)
  | PrettyConfigPlcReadable (PrettyConfigReadable PrettyConfigName)
  deriving stock (Show)

-- | Global configuration used for pretty-printing PLC entities.
data PrettyConfigPlc = PrettyConfigPlc
  { _pcpOptions :: PrettyConfigPlcOptions
  , _pcpStrategy :: PrettyConfigPlcStrategy
  }
  deriving stock (Show)

type instance HasPrettyDefaults PrettyConfigPlc = 'True

-- | The "pretty-printable PLC entity" constraint.
type PrettyPlc = PrettyBy PrettyConfigPlc

-- | A constraint that allows to derive @PrettyBy PrettyConfigPlc@ instances, see below.
type DefaultPrettyPlcStrategy a =
  ( PrettyClassic a
  , PrettyReadable a
  )

instance HasPrettyConfigName PrettyConfigPlcStrategy where
  toPrettyConfigName (PrettyConfigPlcClassic configClassic) = toPrettyConfigName configClassic
  toPrettyConfigName (PrettyConfigPlcReadable configReadable) = toPrettyConfigName configReadable

instance HasPrettyConfigName PrettyConfigPlc where
  toPrettyConfigName = toPrettyConfigName . _pcpStrategy

instance DefaultPrettyPlcStrategy a => PrettyBy PrettyConfigPlcStrategy (PrettyAny a) where
  prettyBy (PrettyConfigPlcClassic configClassic) = prettyBy configClassic . unPrettyAny
  prettyBy (PrettyConfigPlcReadable configReadable) = prettyBy configReadable . unPrettyAny

instance DefaultPrettyPlcStrategy a => PrettyBy PrettyConfigPlc (PrettyAny a) where
  prettyBy = prettyBy . _pcpStrategy

{-| The 'PrettyConfigPlcOptions' used by default:
print errors in full. -}
prettyConfigPlcOptions :: PrettyConfigPlcOptions
prettyConfigPlcOptions = PrettyConfigPlcOptions CondensedErrorsNo

{-| The 'PrettyConfigPlc' used by default:
use the classic view and print neither 'Unique's, nor name attachments. -}
prettyConfigPlcClassic :: PrettyConfigPlcOptions -> PrettyConfigPlc
prettyConfigPlcClassic opts =
  PrettyConfigPlc opts $ PrettyConfigPlcClassic prettyConfigClassic

{-| The 'PrettyConfigPlc' used for debugging:
use the classic view and print 'Unique's, but not name attachments. -}
prettyConfigPlcClassicSimple :: PrettyConfigPlcOptions -> PrettyConfigPlc
prettyConfigPlcClassicSimple opts =
  PrettyConfigPlc opts $ PrettyConfigPlcClassic prettyConfigClassicSimple

{-| The 'PrettyConfigPlc' used by default and for readability:
use the refined view and print 'Unique's but not name attachments. -}
prettyConfigPlcReadable :: PrettyConfigPlcOptions -> PrettyConfigPlc
prettyConfigPlcReadable opts =
  PrettyConfigPlc opts . PrettyConfigPlcReadable $
    botPrettyConfigReadable prettyConfigName def

{-| The 'PrettyConfigPlc' used for debugging and readability:
use the refined view and print neither 'Unique's nor name attachments. -}
prettyConfigPlcReadableSimple :: PrettyConfigPlcOptions -> PrettyConfigPlc
prettyConfigPlcReadableSimple opts =
  PrettyConfigPlc opts . PrettyConfigPlcReadable $
    botPrettyConfigReadable prettyConfigNameSimple def

-- | Pretty-print a PLC value in the default mode using the classic view.
prettyPlcClassic :: PrettyPlc a => a -> Doc ann
prettyPlcClassic = prettyBy $ prettyConfigPlcClassic prettyConfigPlcOptions

-- | Pretty-print a PLC value without unique indices using the classic view.
prettyPlcClassicSimple :: PrettyPlc a => a -> Doc ann
prettyPlcClassicSimple = prettyBy $ prettyConfigPlcClassicSimple prettyConfigPlcOptions

-- | Pretty-print a PLC value in the default mode using the readable view.
prettyPlcReadable :: PrettyPlc a => a -> Doc ann
prettyPlcReadable = prettyBy $ prettyConfigPlcReadable prettyConfigPlcOptions

-- | Pretty-print a PLC value without unique indices using the readable view.
prettyPlcReadableSimple :: PrettyPlc a => a -> Doc ann
prettyPlcReadableSimple = prettyBy $ prettyConfigPlcReadableSimple prettyConfigPlcOptions

{-| Pretty-print a PLC value using the condensed way (see 'CondensedErrors')
of pretty-printing PLC errors (in case there are any). -}
prettyPlcCondensedErrorBy
  :: PrettyPlc a => (PrettyConfigPlcOptions -> PrettyConfigPlc) -> a -> Doc ann
prettyPlcCondensedErrorBy toConfig = prettyBy . toConfig $ PrettyConfigPlcOptions CondensedErrorsYes
