{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
-- Otherwise we get a complaint about the 'fromIntegral' call in the generated instance of 'Integral' for 'Ada'
{-# OPTIONS_GHC -Wno-identities #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
-- | Slots and slot ranges.
module Ledger.Slot(
      Slot(..)
    , SlotRange
    , width
    ) where

import           Codec.Serialise.Class     (Serialise)
import           Data.Aeson                (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import           Data.Hashable             (Hashable)
import           GHC.Generics              (Generic)
import           IOTS                      (IotsType)
import qualified Prelude                   as Haskell
import           Schema                    (FormSchema (FormSchemaSlotRange), ToSchema (toSchema))


import           Language.PlutusTx.Lift    (makeLift)
import           Language.PlutusTx.Prelude

import           Ledger.Interval

{-# ANN module "HLint: ignore Redundant if" #-}

-- | The slot number. This is a good proxy for time, since on the Cardano blockchain
-- slots pass at a constant rate.
newtype Slot = Slot { getSlot :: Integer }
    deriving stock (Haskell.Eq, Haskell.Ord, Show, Generic)
    deriving anyclass (ToSchema, FromJSON, FromJSONKey, ToJSON, ToJSONKey, IotsType)
    deriving newtype (Haskell.Num, AdditiveSemigroup, AdditiveMonoid, AdditiveGroup, Enum, Eq, Ord, Real, Integral, Serialise, Hashable)

makeLift ''Slot

-- | An 'Interval' of 'Slot's.
type SlotRange = Interval Slot

instance ToSchema SlotRange where
  toSchema = FormSchemaSlotRange

{-# INLINABLE width #-}
-- | Number of 'Slot's covered by the interval, if finite. @width (from x) == Nothing@.
width :: SlotRange -> Maybe Integer
width (Interval (LowerBound (Finite (Slot s1)) in1) (UpperBound (Finite (Slot s2)) in2)) =
    let lowestValue = if in1 then s1 else s1 + 1
        highestValue = if in2 then s2 else s2 - 1
    in if lowestValue <= highestValue
    -- +1 avoids fencepost error: width of [2,4] is 3.
    then Just $ (highestValue - lowestValue) + 1
    -- low > high, i.e. empty interval
    else Nothing
-- Infinity is involved!
width _ = Nothing
