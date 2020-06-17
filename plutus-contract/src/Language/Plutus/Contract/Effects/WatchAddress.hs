{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Effects.WatchAddress where

import           Control.Lens                               (at, view, (^.))
import           Data.Map                                   (Map)
import qualified Data.Map                                   as Map
import           Data.Maybe                                 (fromMaybe)
import           Data.Row
import           Ledger                                     (Address, Slot, TxId, Value, txId)
import           Ledger.AddressMap                          (AddressMap, UtxoMap, fundsAt)
import qualified Ledger.AddressMap                          as AM
import           Ledger.Tx                                  (Tx)
import qualified Ledger.Value                               as V

import           Language.Plutus.Contract.Effects.AwaitSlot
import           Language.Plutus.Contract.Request           (ContractRow, requestMaybe)
import           Language.Plutus.Contract.Schema            (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Types             (AsContractError, Contract)
import           Language.Plutus.Contract.Util              (loopM)

type AddressSymbol = "address"

type HasWatchAddress s =
    ( HasType AddressSymbol (Address, Tx) (Input s)
    , HasType AddressSymbol Address (Output s)
    , ContractRow s)

type WatchAddress = AddressSymbol .== ((Address, Tx), Address)

-- | Wait for the next transaction that changes an address.
nextTransactionAt :: forall s e. (AsContractError e, HasWatchAddress s) => Address -> Contract s e Tx
nextTransactionAt addr =
    let check :: (Address, Tx) -> Maybe Tx
        check (addr', tx) = if addr == addr' then Just tx else Nothing
    in
    requestMaybe @AddressSymbol @_ @_ @s addr check

-- | Watch an address until the given slot, then return all known outputs
--   at the address.
watchAddressUntil
    :: forall s e.
       ( HasAwaitSlot s
       , HasWatchAddress s
       , AsContractError e
       )
    => Address
    -> Slot
    -> Contract s e UtxoMap
watchAddressUntil a slot = view (fundsAt a) <$> collectUntil @s AM.updateAddresses (AM.addAddress a mempty) (nextTransactionAt @s a) slot

-- | Watch an address for changes, and return the outputs
--   at that address when the total value at the address
--   has surpassed the given value.
fundsAtAddressGt
    :: forall s e.
       ( HasWatchAddress s
       , AsContractError e
       )
    => Address
    -> Value
    -> Contract s e UtxoMap
fundsAtAddressGt addr vl =
    fundsAtAddressCondition (\presentVal -> presentVal `V.gt` vl) addr

fundsAtAddressCondition
    :: forall s e.
       ( HasWatchAddress s
       , AsContractError e
       )
    => (Value -> Bool)
    -> Address
    -> Contract s e UtxoMap
fundsAtAddressCondition condition addr = view (fundsAt addr) <$> loopM go mempty where
    go cur = do
        delta <- AM.fromTxOutputs <$> nextTransactionAt @s addr
        let cur' = cur <> delta
            presentVal = fromMaybe mempty (AM.values cur' ^. at addr)
        if condition presentVal
        then pure (Right cur') else pure (Left cur')

-- | Watch an address for changes, and return the outputs
--   at that address when the total value at the address
--   has reached or surpassed the given value.
fundsAtAddressGeq
    :: forall s e.
       ( HasWatchAddress s
       , AsContractError e
       )
    => Address
    -> Value
    -> Contract s e UtxoMap
fundsAtAddressGeq addr vl =
    fundsAtAddressCondition (\presentVal -> presentVal `V.geq` vl) addr

-- | Watch the address until the transaction with the given 'TxId' appears
--   on the ledger. Warning: If the transaction does not touch the address,
--   or is invalid, then 'awaitTransactionConfirmed' will not return.
awaitTransactionConfirmed
    :: forall s e.
       ( HasWatchAddress s
       , AsContractError e
       )
    => Address
    -> TxId
    -> Contract s e Tx
awaitTransactionConfirmed addr txid =
    flip loopM () $ \_ -> do
        tx' <- nextTransactionAt addr
        if txId tx' == txid
        then pure $ Right tx'
        else pure $ Left ()

events
    :: forall s.
       ( HasType AddressSymbol (Address, Tx) (Input s)
       , AllUniqueLabels (Input s)
       )
    => AddressMap
    -> Tx
    -> Map Address (Event s)
events utxo tx =
    Map.fromSet
        (\addr -> Event $ IsJust (Label @AddressSymbol) (addr, tx))
        (AM.addressesTouched utxo tx)

watchedAddress
    :: forall s.
    ( HasType AddressSymbol Address (Output s))
    => Handlers s
    -> Maybe Address
watchedAddress (Handlers r) = trial' r (Label @AddressSymbol)
