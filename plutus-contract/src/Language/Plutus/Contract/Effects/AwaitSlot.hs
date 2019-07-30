{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
-- | Wait until a slot number has been reached.
module Language.Plutus.Contract.Effects.AwaitSlot where

import           Control.Eff
import           Control.Eff.Exception
import           Control.Eff.Extend
import           Control.Eff.Reader.Lazy
import           Data.Function                         (fix)

import           Language.Plutus.Contract.Prompt.Event as Event
import           Language.Plutus.Contract.Prompt.Hooks as Hooks
import           Ledger.Slot                           (Slot)

data AwaitSlot v where
  AwaitSlot :: Slot -> AwaitSlot Slot

awaitSlot :: Member AwaitSlot r => Slot -> Eff r Slot
awaitSlot = send . AwaitSlot

instance (Member (Reader (Maybe Event)) r, Member (Exc (Hook ())) r) => Handle AwaitSlot r a k where
  handle step cor req = case req of
    AwaitSlot slot -> step (comp (singleK promptSlot) cor ^$ slot)

promptSlot :: (Member (Reader (Maybe Event)) r, Member (Exc (Hook ())) r) => Slot -> Eff r Slot
promptSlot sl' = do
  sl <- reader (>>= Event.slotChange)
  case sl of
    Just s
      | s >= sl' -> pure s
    _ -> throwError @(Hook ()) (Hooks.slotHook sl')

runAwaitSlot :: (Member (Reader (Maybe Event)) r, Member (Exc (Hook ())) r) => Eff (AwaitSlot ': r) a -> Eff r a
runAwaitSlot = fix (handle_relay pure)
