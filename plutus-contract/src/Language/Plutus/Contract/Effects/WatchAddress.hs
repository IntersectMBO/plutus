{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
-- | Watch an address on the blockchain and receive notifications when it
--   is changed.
module Language.Plutus.Contract.Effects.WatchAddress where

import           Control.Eff
import           Control.Eff.Exception
import           Control.Eff.Extend
import           Control.Eff.Reader.Lazy
import           Data.Function                         (fix)

import           Language.Plutus.Contract.Prompt.Event as Event
import           Language.Plutus.Contract.Prompt.Hooks as Hooks
import           Ledger.Tx                             (Address, Tx)

data WatchAddress v where
  WatchAddress :: Address -> WatchAddress Tx

nextTransactionAt :: Member WatchAddress r => Address -> Eff r Tx
nextTransactionAt = send . WatchAddress

instance (Member (Reader (Maybe Event)) r, Member (Exc (Hook ())) r) => Handle WatchAddress r a k where
  handle step cor req = case req of
    WatchAddress addr -> step (comp (singleK promptAddress) cor ^$ addr)

runWatchAddress :: (Member (Reader (Maybe Event)) r, Member (Exc (Hook ())) r) => Eff (WatchAddress ': r) a -> Eff r a
runWatchAddress = fix (handle_relay pure)

promptAddress :: (Member (Reader (Maybe Event)) r, Member (Exc (Hook ())) r) => Address -> Eff r Tx
promptAddress addr = do
  sl <- reader (>>= Event.ledgerUpdate)
  case sl of
    Just (addr', tx)
      | addr' == addr -> pure tx
    _ -> throwError @(Hook ()) (Hooks.addrHook addr)
