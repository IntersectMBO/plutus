-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}

-- Otherwise we get a complaint about the 'fromIntegral' call in the generated instance of 'Integral' for 'Ada'
{-# OPTIONS_GHC -Wno-identities #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

-- | UTCTime and UTCTime ranges.
module PlutusLedgerApi.V1.Time
    ( POSIXTime(..)
    , POSIXTimeRange
    , DiffMilliSeconds(..)
    , fromMilliSeconds
    ) where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Interval
import PlutusTx qualified
import PlutusTx.Prelude
import Prelude qualified as Haskell
import Prettyprinter (Pretty (pretty), (<+>))


-- | This is a length of time, as measured by a number of milliseconds.
newtype DiffMilliSeconds = DiffMilliSeconds Integer
  deriving stock (Haskell.Eq, Haskell.Ord, Haskell.Show, Generic)
  deriving anyclass (NFData)
  deriving newtype (Haskell.Num, AdditiveSemigroup, AdditiveMonoid, AdditiveGroup, Haskell.Enum, Eq, Ord, Haskell.Real, Haskell.Integral, PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)

PlutusTx.makeLift ''DiffMilliSeconds
-- See Note [Passing the ScriptContext as a term]
PlutusTx.defaultMakeLiftU ''DiffMilliSeconds

-- | POSIX time is measured as the number of /milliseconds/ since 1970-01-01T00:00:00Z.
-- This is not the same as Haskell's `Data.Time.Clock.POSIX.POSIXTime`
newtype POSIXTime = POSIXTime { getPOSIXTime :: Integer }
  deriving stock (Haskell.Eq, Haskell.Ord, Haskell.Show, Generic)
  deriving anyclass (NFData)
  deriving newtype (AdditiveSemigroup, AdditiveMonoid, AdditiveGroup, Eq, Ord, Enum, PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
  deriving newtype (Haskell.Num, Haskell.Enum, Haskell.Real, Haskell.Integral)

PlutusTx.makeLift ''POSIXTime
-- See Note [Passing the ScriptContext as a term]
PlutusTx.defaultMakeLiftU ''POSIXTime

instance Pretty POSIXTime where
  pretty (POSIXTime i) = "POSIXTime" <+> pretty i

-- | An 'Interval' of 'POSIXTime's.
type POSIXTimeRange = Interval POSIXTime

-- | Simple conversion from 'DiffMilliSeconds' to 'POSIXTime'.
{-# INLINABLE fromMilliSeconds #-}
fromMilliSeconds :: DiffMilliSeconds -> POSIXTime
fromMilliSeconds (DiffMilliSeconds s) = POSIXTime s
