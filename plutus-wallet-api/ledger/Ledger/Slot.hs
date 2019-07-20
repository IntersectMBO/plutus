{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
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
    , singleton
    , width
    ) where

import           Codec.Serialise.Class        (Serialise)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Hashable                (Hashable)
import           Data.Swagger.Internal.Schema (ToSchema)
import           GHC.Generics                 (Generic)
import qualified Prelude                      as Haskell

import           Language.PlutusTx.Lift       (makeLift)
import           Language.PlutusTx.Prelude

import           Ledger.Interval

{-# ANN module "HLint: ignore Redundant if" #-}

-- | The slot number. This is a good proxy for time, since on the Cardano blockchain
-- slots pass at a constant rate.
newtype Slot = Slot { getSlot :: Integer }
    deriving stock (Haskell.Eq, Haskell.Ord, Show, Generic)
    deriving anyclass (ToSchema, FromJSON, ToJSON)
    deriving newtype (Num, Enum, Eq, Ord, Real, Integral, Serialise, Hashable)

makeLift ''Slot

-- | An 'Interval' of 'Slot's.
type SlotRange = Interval Slot

-- | A 'SlotRange' that covers only a single slot.
singleton :: Slot -> SlotRange
singleton (Slot s) = Interval (Just (Slot s)) (Just (Slot (plus s 1)))

-- | Number of 'Slot's covered by the interval. @width (from x) == Nothing@.
width :: SlotRange -> Maybe Integer
width (Interval f t) = case f of
    Nothing -> Nothing
    Just (Slot f') -> case t of
        Nothing        -> Nothing
        Just (Slot t') -> Just (minus t' f')
