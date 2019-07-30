{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds   #-}
module Language.Plutus.Contract(
      Contract
    , ContractActions
    -- * Dealing with time
    , AwaitSlot
    , awaitSlot
    , until
    , when
    , timeout
    , between
    , collectUntil
    -- * Endpoints
    , ExposeEndpoint
    , endpoint
    -- * Transactions
    , WriteTx
    , writeTx
    -- * Blockchain events
    , WatchAddress
    , nextTransactionAt
    , watchAddressUntil
    , fundsAtAddressGt
    -- * Conveniences
    , module X
    -- * Etc
    , convertContract
    ) where

import           Control.Eff
import           Control.Eff.Exception
import           Control.Eff.Reader.Lazy
import           Control.Lens
import           Data.Aeson                                      (FromJSON)
import           Data.Maybe                                      (fromMaybe)

import           Language.Plutus.Contract.Effects                (AwaitSlot, ContractActions, ContractEffects,
                                                                  ExposeEndpoint, WatchAddress, WriteTx, runEffects)
import qualified Language.Plutus.Contract.Effects.AwaitSlot      as Slot
import qualified Language.Plutus.Contract.Effects.ExposeEndpoint as Endpoint
import qualified Language.Plutus.Contract.Effects.WatchAddress   as Addr
import qualified Language.Plutus.Contract.Effects.WriteTx        as Tx
import           Language.Plutus.Contract.Prompt.Event           (Event)
import           Language.Plutus.Contract.Prompt.Hooks           (Hooks, hooks)
import           Language.Plutus.Contract.Resumable              (Resumable, Step (..), mapStep, step)
import           Language.Plutus.Contract.Tx                     (UnbalancedTx)
import           Language.Plutus.Contract.Util                   as X
import           Ledger.AddressMap                               (AddressMap)
import qualified Ledger.AddressMap                               as AM
import           Ledger.Slot                                     (Slot)
import           Ledger.Tx                                       (Address, Tx)
import           Ledger.Value                                    (Value)
import qualified Ledger.Value                                    as V

import           Prelude                                         hiding (until)

type Contract r a = Resumable (Eff r) a

awaitSlot :: (Member AwaitSlot r) => Slot -> Contract r Slot
awaitSlot = step . Slot.awaitSlot

-- | Run a contract until the given slot has been reached.
until :: (Member AwaitSlot r) => Contract r a -> Slot -> Contract r (Maybe a)
until c sl = do
    awaited <- selectEither (awaitSlot sl) c
    pure $ case awaited of
        Left _  -> Nothing
        Right a -> Just a

-- | Run a contract when the given slot has been reached.
when :: (Member AwaitSlot r) => Slot -> Contract r a -> Contract r a
when s c = awaitSlot s >> c

-- | Run a contract until the given slot has been reached.
--   @timeout = flip until@
timeout :: (Member AwaitSlot r) =>  Slot -> Contract r a -> Contract r (Maybe a)
timeout = flip until

-- | Wait until the first slot is reached, then run the contract until
--   the second slot is reached.
between :: (Member AwaitSlot r) => Slot -> Slot -> Contract r a -> Contract r (Maybe a)
between a b = timeout b . when a

-- | Repeatedly run a contract until the slot is reached, then
--   return the last result.
collectUntil :: (Member AwaitSlot r) => (a -> b -> b) -> b -> Contract r a -> Slot -> Contract r b
collectUntil f b con s = foldMaybe f b (until con s)

-- | Expose an endpoint, return the data that was entered
endpoint :: forall a. forall r. (FromJSON a, Member ExposeEndpoint r) => String -> Contract r a
endpoint = step . Endpoint.exposeEndpoint

--  | Send an unbalanced transaction to the wallet.
writeTx :: (Member WriteTx r) => UnbalancedTx -> Contract r ()
writeTx = step . Tx.writeTx

-- | Wait for the next transaction that changes an address.
nextTransactionAt :: (Member WatchAddress r) => Address -> Contract r Tx
nextTransactionAt = step . Addr.nextTransactionAt

-- | Watch an address until the given slot, then return all known outputs
--   at the address.
watchAddressUntil :: (Member AwaitSlot r, Member WatchAddress r) => Address -> Slot -> Contract r AddressMap
watchAddressUntil a = collectUntil AM.updateAddresses (AM.addAddress a mempty) (nextTransactionAt a)

-- | Watch an address for changes, and return the outputs
--   at that address when the total value at the address
--   has surpassed the given value.
fundsAtAddressGt :: (Member WatchAddress r) => Address -> Value -> Contract r AddressMap
fundsAtAddressGt addr' vl = loopM go mempty where
    go cur = do
        delta <- AM.fromTxOutputs <$> nextTransactionAt addr'
        let cur' = cur <> delta
            presentVal = fromMaybe mempty (AM.values cur' ^. at addr')
        if presentVal `V.gt` vl
        then pure (Left cur') else pure (Right cur')

-- | Take a single step in form of 'Eff (ContractEffects []) a' and attempt to
--   run it on the given 'Event' (or 'Nothing'). If it fails, return a
--   description of the data that is needed (the 'Hooks'). If it succeeds,
--   return the result. See note [Contract Effects].
convertStep :: Eff (ContractEffects '[]) a -> Step (Maybe Event) (Either String Hooks) a
convertStep st = Step $ \i -> either (Left . Left) (either (Left . Right . hooks) Right) . run . runError . runError . runReader i . runEffects $ st

convertContract :: Resumable (Eff (ContractEffects '[])) a -> Resumable (Step (Maybe Event) (Either String Hooks)) a
convertContract = mapStep convertStep
