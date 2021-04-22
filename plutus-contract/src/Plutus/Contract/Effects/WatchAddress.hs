{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Plutus.Contract.Effects.WatchAddress(
    AddressSymbol,
    HasWatchAddress,
    WatchAddress,
    addressChangeRequest,
    nextTransactionsAt,
    fundsAtAddressGt,
    fundsAtAddressGeq,
    events,
    watchAddressRequest,
    watchedAddress,
    AddressChangeRequest(..),
    AddressChangeResponse(..),
    event
    ) where

import           Data.Map                          (Map)
import qualified Data.Map                          as Map
import           Data.Row
import           Ledger                            (Address, Slot, Value)
import           Ledger.AddressMap                 (AddressMap, UtxoMap)
import qualified Ledger.AddressMap                 as AM
import qualified Ledger.Interval                   as Interval
import           Ledger.Tx                         (Tx, txOutTxOut, txOutValue)
import qualified Ledger.Value                      as V
import           Plutus.Contract.Effects.AwaitSlot (HasAwaitSlot, awaitSlot, currentSlot)
import           Plutus.Contract.Effects.UtxoAt    (HasUtxoAt, utxoAt)
import           Plutus.Contract.Request           (ContractRow, requestMaybe)
import           Plutus.Contract.Schema            (Event (..), Handlers (..), Input, Output)
import           Plutus.Contract.Types             (AsContractError, Contract)
import           Plutus.Contract.Util              (loopM)
import           Wallet.Types                      (AddressChangeRequest (..), AddressChangeResponse (..))

type AddressSymbol = "address"

type HasWatchAddress s =
    ( HasType AddressSymbol AddressChangeResponse (Input s)
    , HasType AddressSymbol AddressChangeRequest (Output s)
    , ContractRow s)

type WatchAddress = AddressSymbol .== (AddressChangeResponse, AddressChangeRequest)

{-| Get the transactions that modified an address in a specific slot.
-}
addressChangeRequest ::
    forall w s e.
    ( HasWatchAddress s
    , AsContractError e
    )
    => AddressChangeRequest
    -> Contract w s e AddressChangeResponse
addressChangeRequest rq =
    let check :: AddressChangeResponse -> Maybe AddressChangeResponse
        check r@AddressChangeResponse{acrAddress, acrSlotRange}
                | acrAddress == acreqAddress rq && acrSlotRange >= acreqSlotRange rq = Just r
                | otherwise = Nothing
    in requestMaybe @w @AddressSymbol @_ @_ @s rq check

-- | Call 'addresssChangeRequest' for the address in each slot, until at least one
--   transaction is returned that modifies the address.
nextTransactionsAt ::
    forall w s e.
    ( HasWatchAddress s
    , AsContractError e
    , HasAwaitSlot s
    )
    => Address
    -> Contract w s e [Tx]
nextTransactionsAt addr = do
    initial <- currentSlot
    let go sl = do
            txns <- acrTxns <$> addressChangeRequest AddressChangeRequest
                { acreqSlotRange = Interval.singleton sl
                , acreqAddress = addr
                }

            if null txns
                then go (succ sl)
                else pure txns
    go initial

-- | Watch an address for changes, and return the outputs
--   at that address when the total value at the address
--   has surpassed the given value.
fundsAtAddressGt
    :: forall w s e.
       ( AsContractError e
       , HasAwaitSlot s
       , HasUtxoAt s
       )
    => Address
    -> Value
    -> Contract w s e UtxoMap
fundsAtAddressGt addr vl =
    fundsAtAddressCondition (\presentVal -> presentVal `V.gt` vl) addr

fundsAtAddressCondition
    :: forall w s e.
       ( AsContractError e
       , HasAwaitSlot s
       , HasUtxoAt s
       )
    => (Value -> Bool)
    -> Address
    -> Contract w s e UtxoMap
fundsAtAddressCondition condition addr = loopM go () where
    go () = do
        cur <- utxoAt addr
        sl <- currentSlot
        let presentVal = foldMap (txOutValue . txOutTxOut) cur
        if condition presentVal
            then pure (Right cur)
            else awaitSlot (sl + 1) >> pure (Left ())

-- | Watch an address for changes, and return the outputs
--   at that address when the total value at the address
--   has reached or surpassed the given value.
fundsAtAddressGeq
    :: forall w s e.
       ( AsContractError e
       , HasAwaitSlot s
       , HasUtxoAt s
       )
    => Address
    -> Value
    -> Contract w s e UtxoMap
fundsAtAddressGeq addr vl =
    fundsAtAddressCondition (\presentVal -> presentVal `V.geq` vl) addr

-- | The 'AddressChangeResponse' events for all addresses touched by the
--   transaction. The 'AddressMap' is used to lookup the addresses of outputs
--   spent by the transaction.
events
    :: forall s.
       ( HasType AddressSymbol AddressChangeResponse (Input s)
       , AllUniqueLabels (Input s)
       )
    => Slot
    -> AddressMap
    -> Tx
    -> Map Address (Event s)
events sl utxo tx =
    let mkEvent addr = AddressChangeResponse{acrAddress=addr,acrSlotRange=Interval.singleton sl,acrTxns=[tx]}
    in Map.fromSet
        (Event . IsJust (Label @AddressSymbol) . mkEvent)
        (AM.addressesTouched utxo tx)

watchAddressRequest
    :: forall s.
    ( HasType AddressSymbol AddressChangeRequest (Output s))
    => Handlers s
    -> Maybe AddressChangeRequest
watchAddressRequest (Handlers r) = trial' r (Label @AddressSymbol)

watchedAddress
    :: forall s.
    ( HasType AddressSymbol AddressChangeRequest (Output s))
    => Handlers s
    -> Maybe Address
watchedAddress = fmap acreqAddress . watchAddressRequest

event
    :: forall s.
       ( HasType AddressSymbol AddressChangeResponse (Input s)
       , AllUniqueLabels (Input s)
       )
    => AddressChangeResponse
    -> Event s
event = Event . IsJust (Label @AddressSymbol)
