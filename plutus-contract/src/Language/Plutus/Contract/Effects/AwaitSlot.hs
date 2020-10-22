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
import           Data.Text.Prettyprint.Doc.Extras
import           GHC.Generics                     (Generic)
import           IOTS                             (IotsType)
import           Prelude                          hiding (until)

import           Language.Plutus.Contract.Request as Req
import           Language.Plutus.Contract.Schema  (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Types   (AsContractError, Contract, selectEither)
import           Language.Plutus.Contract.Util    (foldMaybe)

import           Ledger.Slot                      (Slot (..))

type SlotSymbol = "slot"

type HasAwaitSlot s =
  ( HasType SlotSymbol Slot (Input s)
  , HasType SlotSymbol WaitingForSlot (Output s)
  , ContractRow s
  )

newtype WaitingForSlot = WaitingForSlot { unWaitingForSlot :: Slot }
  deriving stock (Eq, Ord, Show, Generic)
  deriving Pretty via (Tagged "WaitingForSlot:" Slot)
  deriving anyclass (ToJSON, FromJSON, IotsType)

type AwaitSlot = SlotSymbol .== (Slot, WaitingForSlot)

-- | A contract that waits until the slot is reached, then returns the
--   current slot.
awaitSlot
    :: forall s e.
       ( HasAwaitSlot s
       , AsContractError e
       )
    => Slot
    -> Contract s e Slot
awaitSlot sl =
  let s = WaitingForSlot sl
      check :: Slot -> Maybe Slot
      check sl' = if sl' >= sl then Just sl' else Nothing
  in
  requestMaybe @SlotSymbol @_ @_ @s s check

-- | Wait for a number of slots.
waitNSlots
  :: forall s e.
     ( HasAwaitSlot s
     , AsContractError e
     )
  => Integer
  -> Contract s e Slot
waitNSlots i = do
  Slot current <- currentSlot
  awaitSlot $ Slot (current + i)

event
    :: forall s.
    ( HasType SlotSymbol Slot (Input s)
    , AllUniqueLabels (Input s))
    => Slot
    -> Event s
event = Event . IsJust #slot

request
    :: forall s.
    ( HasType SlotSymbol WaitingForSlot (Output s))
    => Handlers s
    -> Maybe Slot
request (Handlers r) = unWaitingForSlot <$> trial' r (Label @SlotSymbol)

-- | Run a contract until the given slot has been reached.
until
  :: forall s e a.
     ( HasAwaitSlot s
     , AsContractError e
     )
  => Contract s e a
  -> Slot
  -> Contract s e (Maybe a)
until c sl =
  fmap (either (const Nothing) Just) (selectEither (awaitSlot @s sl) c)

-- | Run a contract when the given slot has been reached.
when
  :: forall s e a.
     ( HasAwaitSlot s
     , AsContractError e
     )
  => Slot
  -> Contract s e a
  -> Contract s e a
when s c = awaitSlot @s s >> c

-- | Run a contract until the given slot has been reached.
--   @timeout = flip until@
timeout
  :: forall s e a.
     ( HasAwaitSlot s
     , AsContractError e
     )
  => Slot
  -> Contract s e a
  -> Contract s e (Maybe a)
timeout = flip (until @s)

-- | Wait until the first slot is reached, then run the contract until
--   the second slot is reached.
between
  :: forall s e a.
     ( HasAwaitSlot s
     , AsContractError e
     )
  => Slot
  -> Slot
  -> Contract s e a
  -> Contract s e (Maybe a)
between a b = timeout @s b . when @s a

-- | Repeatedly run a contract until the slot is reached, then
--   return the last result.
collectUntil
  :: forall s e a b.
     ( HasAwaitSlot s
     , AsContractError e
     )
  => (a -> b -> b)
  -> b
  -> Contract s e a
  -> Slot
  -> Contract s e b
collectUntil f b con s = foldMaybe f b (until @s con s)

-- | The current slot number
currentSlot
  :: forall s e.
  ( HasAwaitSlot s
  , AsContractError e
  )
  => Contract s e Slot
currentSlot = awaitSlot 0
