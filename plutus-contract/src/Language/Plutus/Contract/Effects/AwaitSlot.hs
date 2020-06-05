{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Effects.AwaitSlot where

import           Data.Aeson                       (FromJSON, ToJSON)
import           Data.Row
import           Data.Semigroup                   (Min (..))
import           Data.Text.Prettyprint.Doc.Extras
import           GHC.Generics                     (Generic)
import           IOTS                             (IotsType)
import           Prelude                          hiding (until)

import           Language.Plutus.Contract.Request as Req
import           Language.Plutus.Contract.Schema  (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Util    (foldMaybe, selectEither)

import           Ledger.Slot                      (Slot)

type SlotSymbol = "slot"

type HasAwaitSlot s =
  ( HasType SlotSymbol Slot (Input s)
  , HasType SlotSymbol WaitingForSlot (Output s)
  , ContractRow s
  )

newtype WaitingForSlot = WaitingForSlot { unWaitingForSlot :: Maybe Slot }
  deriving stock (Eq, Ord, Show, Generic)
  deriving Semigroup via Maybe (Min Slot)
  deriving Monoid via Maybe (Min Slot)
  deriving Pretty via (Tagged "WaitingForSlot:" (Maybe Slot))
  deriving anyclass (ToJSON, FromJSON, IotsType)

type AwaitSlot = SlotSymbol .== (Slot, WaitingForSlot)

-- | A contract that waits until the slot is reached, then returns the
--   current slot.
awaitSlot
    :: forall s e.
       (HasAwaitSlot s)
    => Slot
    -> Contract s e Slot
awaitSlot sl =
  let s = WaitingForSlot $ Just sl
      check :: Slot -> Maybe Slot
      check sl' = if sl' >= sl then Just sl' else Nothing
  in
  requestMaybe @SlotSymbol @_ @_ @s s check

event
    :: forall s.
    ( HasType SlotSymbol Slot (Input s)
    , AllUniqueLabels (Input s))
    => Slot
    -> Event s
event = Event . IsJust #slot

nextSlot
    :: forall s.
    ( HasType SlotSymbol WaitingForSlot (Output s))
    => Handlers s
    -> Maybe Slot
nextSlot (Handlers r) = unWaitingForSlot (r .! #slot)


-- | Run a contract until the given slot has been reached.
until
  :: forall s e a.
     (HasAwaitSlot s)
  => Contract s e a
  -> Slot
  -> Contract s e (Maybe a)
until c sl =
  fmap (either (const Nothing) Just) (selectEither (awaitSlot @s sl) c)

-- | Run a contract when the given slot has been reached.
when
  :: forall s e a.
     (HasAwaitSlot s)
  => Slot
  -> Contract s e a
  -> Contract s e a
when s c = awaitSlot @s s >> c

-- | Run a contract until the given slot has been reached.
--   @timeout = flip until@
timeout
  :: forall s e a.
     (HasAwaitSlot s)
  => Slot
  -> Contract s e a
  -> Contract s e (Maybe a)
timeout = flip (until @s)

-- | Wait until the first slot is reached, then run the contract until
--   the second slot is reached.
between
  :: forall s e a.
     (HasAwaitSlot s)
  => Slot
  -> Slot
  -> Contract s e a
  -> Contract s e (Maybe a)
between a b = timeout @s b . when @s a

-- | Repeatedly run a contract until the slot is reached, then
--   return the last result.
collectUntil
  :: forall s e a b.
     (HasAwaitSlot s)
  => (a -> b -> b)
  -> b
  -> Contract s e a
  -> Slot
  -> Contract s e b
collectUntil f b con s = foldMaybe f b (until @s con s)
