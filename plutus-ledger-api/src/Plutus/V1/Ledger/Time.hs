{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
-- Otherwise we get a complaint about the 'fromIntegral' call in the generated instance of 'Integral' for 'Ada'
{-# OPTIONS_GHC -Wno-identities #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

-- | UTCTime and UTCTime ranges.
module Plutus.V1.Ledger.Time(
      POSIXTime(..)
    , POSIXTimeRange
    ) where

import           Codec.Serialise.Class     (Serialise)
import           Control.DeepSeq           (NFData)
import           Data.Aeson                (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import           Data.Hashable             (Hashable)
import           Data.Text.Prettyprint.Doc (Pretty (pretty), comma, (<+>))
import           GHC.Generics              (Generic)
import qualified Prelude                   as Haskell

import qualified PlutusTx
import           PlutusTx.Lift             (makeLift)
import           PlutusTx.Prelude

import           Plutus.V1.Ledger.Interval

-- | POSIX time is measured as the number of seconds since 1970-01-01 00:00 UTC
newtype POSIXTime = POSIXTime { getPOSIXTime :: Integer }
  deriving stock (Haskell.Eq, Haskell.Ord, Haskell.Show, Generic)
  deriving anyclass (FromJSON, FromJSONKey, ToJSON, ToJSONKey, NFData)
  deriving newtype (Haskell.Num, AdditiveSemigroup, AdditiveMonoid, AdditiveGroup, Haskell.Enum, Eq, Ord, Haskell.Real, Haskell.Integral, Serialise, Hashable, PlutusTx.IsData)

makeLift ''POSIXTime

instance Pretty POSIXTime where
  pretty (POSIXTime i) = "POSIXTime" <+> pretty i

instance Pretty (Interval POSIXTime) where
  pretty (Interval l h) = pretty l <+> comma <+> pretty h

-- | An 'Interval' of 'POSIXTime's.
type POSIXTimeRange = Interval POSIXTime
