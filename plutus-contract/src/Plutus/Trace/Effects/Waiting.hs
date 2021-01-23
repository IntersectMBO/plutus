{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
-- | Waiting for things to happen
module Plutus.Trace.Effects.Waiting(
    Waiting(..)
    , waitUntilSlot
    , nextSlot
    , waitNSlots
    , handleWaiting
    ) where

import           Control.Monad.Freer           (Eff, Member, type (~>))
import           Control.Monad.Freer.Coroutine (Yield)
import           Control.Monad.Freer.TH        (makeEffect)
import           Ledger.Slot                   (Slot)
import           Numeric.Natural               (Natural)
import           Plutus.Trace.Emulator.Types   (EmulatorMessage (NewSlot))
import           Plutus.Trace.Scheduler        (Priority (Sleeping), SystemCall, sleep)

data Waiting r where
    WaitUntilSlot :: Slot -> Waiting Slot

makeEffect ''Waiting

-- | Wait until the beginning of the next slot, returning
--   the new slot number.
nextSlot :: Member Waiting effs => Eff effs Slot
nextSlot = waitUntilSlot 0

-- | Wait for a number of slots
waitNSlots ::
    forall effs.
    ( Member Waiting effs )
    => Natural
    -> Eff effs Slot
waitNSlots n
    | n > 1 = nextSlot >> waitNSlots (n - 1)
    | otherwise = nextSlot

handleWaiting ::
    forall effs effs2.
    ( Member (Yield (SystemCall effs2 EmulatorMessage) (Maybe EmulatorMessage)) effs
    )
    => Waiting
    ~> Eff effs
handleWaiting = \case
    WaitUntilSlot s -> go where
        go = sleep @effs2 Sleeping >>= \case { Just (NewSlot _ sl) | sl >= s -> pure sl; _ -> go }
