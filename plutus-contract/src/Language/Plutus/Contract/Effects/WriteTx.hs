{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
-- | Write an 'UnbalancedTx' to be transferred to the wallet for
--   balancing and signing.
module Language.Plutus.Contract.Effects.WriteTx where

import           Language.Plutus.Contract.Tx

import           Control.Eff
import           Control.Eff.Exception
import           Control.Eff.Extend
import           Control.Eff.Reader.Lazy
import           Data.Function                         (fix)
import           Language.Plutus.Contract.Prompt.Event as Event
import           Language.Plutus.Contract.Prompt.Hooks as Hooks

data WriteTx v where
  WriteTx :: UnbalancedTx -> WriteTx ()

writeTx :: Member WriteTx r => UnbalancedTx -> Eff r ()
writeTx tx = send $ WriteTx tx

instance (Member (Reader (Maybe Event)) r, Member (Exc (Hook ())) r) => Handle WriteTx r a k where
  handle step cor req = case req of
    WriteTx t -> step (comp (singleK promptTx) cor ^$ t)

runWriteTx :: (Member (Reader (Maybe Event)) r, Member (Exc (Hook ())) r) => Eff (WriteTx ': r) a -> Eff r a
runWriteTx = fix (handle_relay pure)

promptTx :: (Member (Reader (Maybe Event)) r, Member (Exc (Hook ())) r) => UnbalancedTx -> Eff r ()
promptTx t = do
  sl <- reader (>>= Event.txSubmissionEvent)
  case sl of
    Just () -> pure ()
    _       -> throwError @(Hook ()) (Hooks.txHook t)
