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
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
-- | Slots and slot ranges.
module Ledger.Slot(
      Slot(..)
    , SlotRange
    , singleton
    , empty
    , member
    , width
    , contains
    , before
    , after
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
    deriving (Haskell.Eq, Haskell.Ord, Show, Enum)
    deriving stock (Generic)
    deriving anyclass (ToSchema, FromJSON, ToJSON)
    deriving newtype (Num, Eq, Ord, Real, Integral, Serialise, Hashable)

makeLift ''Slot

-- | An 'Interval' of 'Slot's.
type SlotRange = Interval Slot

-- | A 'SlotRange' that covers only a single slot.
singleton :: Slot -> SlotRange
singleton (Slot s) = Interval (Just (Slot s)) (Just (Slot (plus s 1)))

-- | Check if a 'SlotRange' is empty.
empty :: SlotRange -> Bool
empty (Interval f t) = case f of
    Nothing -> False
    Just f' -> case t of
        Nothing -> False
        Just t' -> f' <= t'

-- | Check if 'Slot' is contained in a 'SlotRange'.
member :: Slot -> SlotRange -> Bool
member s (Interval f t) =
    let lw = case f of { Nothing -> True; Just f' -> f' <= s; }
        hg = case t of { Nothing -> True; Just t' -> t' > s; }
    in
        if lw then hg else False

-- | Number of 'Slot's covered by the interval. @width (from x) == Nothing@.
width :: SlotRange -> Maybe Integer
width (Interval f t) = case f of
    Nothing -> Nothing
    Just (Slot f') -> case t of
        Nothing        -> Nothing
        Just (Slot t') -> Just (minus t' f')

-- | @a `contains` b@ is true if the 'SlotRange' @b@ is entirely contained in
--   @a@. That is, @a `contains` b@ if for every slot @s@, if @member s b@ then
--   @member s a@.
contains :: SlotRange -> SlotRange -> Bool
contains (Interval af at) (Interval bf bt) =
    let lw = case af of
            Nothing -> True
            Just af' -> case bf of
                Nothing  -> False
                Just bf' -> af' <= bf'
        hg = case at of
            Nothing -> True
            Just at' -> case bt of
                Nothing  -> False
                Just bt' -> at' >= bt'
    in
        if lw then hg else False

-- | Check if a 'Slot' is earlier than the beginning of a 'SlotRange'.
before :: Slot -> SlotRange -> Bool
before h (Interval f _) = case f of { Nothing -> False; Just h' -> h' > h; }

-- | Check if a 'Slot' is later than the end of a 'SlotRange'
after :: Slot -> SlotRange -> Bool
after h (Interval _ t) = case t of { Nothing -> False; Just t' -> h >= t'; }
