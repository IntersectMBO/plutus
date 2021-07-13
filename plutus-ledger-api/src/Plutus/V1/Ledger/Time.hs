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
    , DiffMilliSeconds(..)
    , fromMilliSeconds
    ) where

import           Codec.Serialise.Class     (Serialise)
import           Control.DeepSeq           (NFData)
import           Data.Aeson                (FromJSON (parseJSON), FromJSONKey, ToJSON (toJSON), ToJSONKey,
                                            Value (Number))
import           Data.Aeson.Types          (prependFailure, typeMismatch)
import           Data.Hashable             (Hashable)
import           Data.Scientific           (floatingOrInteger, scientific)
import           Data.Text.Prettyprint.Doc (Pretty (pretty), comma, (<+>))
import           GHC.Generics              (Generic)
import           Plutus.V1.Ledger.Interval
import qualified PlutusTx
import           PlutusTx.Lift             (makeLift)
import           PlutusTx.Prelude
import qualified Prelude                   as Haskell


-- | This is a length of time, as measured by a number of milliseconds.
newtype DiffMilliSeconds = DiffMilliSeconds Integer
  deriving stock (Haskell.Eq, Haskell.Ord, Haskell.Show, Generic)
  deriving anyclass (FromJSON, FromJSONKey, ToJSON, ToJSONKey, NFData)
  deriving newtype (Haskell.Num, AdditiveSemigroup, AdditiveMonoid, AdditiveGroup, Haskell.Enum, Eq, Ord, Haskell.Real, Haskell.Integral, Serialise, Hashable, PlutusTx.IsData)

makeLift ''DiffMilliSeconds

-- | POSIX time is measured as the number of milliseconds since 1970-01-01T00:00:00Z
newtype POSIXTime = POSIXTime { getPOSIXTime :: Integer }
  deriving stock (Haskell.Eq, Haskell.Ord, Haskell.Show, Generic)
  deriving anyclass (FromJSONKey, ToJSONKey, NFData)
  deriving newtype (AdditiveSemigroup, AdditiveMonoid, AdditiveGroup, Eq, Ord, Enum, PlutusTx.IsData)
  deriving newtype (Haskell.Num, Haskell.Enum, Haskell.Real, Haskell.Integral, Serialise, Hashable)

-- | Custom `FromJSON` instance which allows to parse a JSON number to a
-- 'POSIXTime' value. The parsed JSON value MUST be an 'Integer' or else the
-- parsing fails.
instance FromJSON POSIXTime where
  parseJSON v@(Number n) =
      either (\_ -> prependFailure "parsing POSIXTime failed, " (typeMismatch "Integer" v))
             (return . POSIXTime)
             (floatingOrInteger n :: Either Haskell.Double Integer)
  parseJSON invalid =
      prependFailure "parsing POSIXTime failed, " (typeMismatch "Number" invalid)

-- | Custom 'ToJSON' instance which allows to simply convert a 'POSIXTime'
-- value to a JSON number.
instance ToJSON POSIXTime where
  toJSON (POSIXTime n) = Number $ scientific n 0

makeLift ''POSIXTime

instance Pretty POSIXTime where
  pretty (POSIXTime i) = "POSIXTime" <+> pretty i

instance Pretty (Interval POSIXTime) where
  pretty (Interval l h) = pretty l <+> comma <+> pretty h

-- | An 'Interval' of 'POSIXTime's.
type POSIXTimeRange = Interval POSIXTime

-- | Simple conversion from 'DiffMilliSeconds' to 'POSIXTime'.
{-# INLINABLE fromMilliSeconds #-}
fromMilliSeconds :: DiffMilliSeconds -> POSIXTime
fromMilliSeconds (DiffMilliSeconds s) = POSIXTime s
