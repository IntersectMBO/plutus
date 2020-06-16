{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
module Language.Plutus.Contract.Effects.WatchAddress where

import           Data.Aeson                                 (FromJSON, ToJSON)
import           Data.Map                                   (Map)
import qualified Data.Map                                   as Map
import           Data.Row
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                               (Generic)
import           Ledger                                     (Address, Slot, TxId, Value, txId)
import           Ledger.AddressMap                          (AddressMap, UtxoMap)
import qualified Ledger.AddressMap                          as AM
import           Ledger.Tx                                  (Tx, txOutTxOut, txOutValue)
import qualified Ledger.Value                               as V

import           Language.Plutus.Contract.Effects.AwaitSlot (HasAwaitSlot, currentSlot)
import           Language.Plutus.Contract.Effects.UtxoAt    (HasUtxoAt, utxoAt)
import           Language.Plutus.Contract.Request           (ContractRow, requestMaybe)
import           Language.Plutus.Contract.Schema            (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Types             (AsContractError, Contract)
import           Language.Plutus.Contract.Util              (loopM)

type AddressSymbol = "address"

type HasWatchAddress s =
    ( HasType AddressSymbol AddressChangeResponse (Input s)
    , HasType AddressSymbol AddressChangeRequest (Output s)
    , ContractRow s)

type WatchAddress = AddressSymbol .== (AddressChangeResponse, AddressChangeRequest)

-- | Information about transactions that spend or produce an output at
--   an address. The transactions are returned in the order they appear
--   in the ledger (oldest first).
data AddressChangeResponse =
    AddressChangeResponse
        { acrAddress :: Address
        , acrSlot    :: Slot
        , acrTx      :: Tx
        }
        deriving stock (Eq, Generic, Show)
        deriving anyclass (ToJSON, FromJSON)

instance Pretty AddressChangeResponse where
    pretty AddressChangeResponse{acrAddress, acrTx, acrSlot} =
        hang 2 $ vsep
            [ "Address:" <+> pretty acrAddress
            , "Slot:" <+> pretty acrSlot
            , "TxId:" <+> pretty (txId acrTx)
            ]

data AddressChangeRequest =
    AddressChangeRequest
        { acreqSlot    :: Slot
        , acreqAddress :: Address
        , acreqTxId    :: Maybe TxId
        }
        deriving stock (Eq, Generic, Show, Ord)
        deriving anyclass (ToJSON, FromJSON)

instance Pretty AddressChangeRequest where
    pretty AddressChangeRequest{acreqSlot, acreqAddress, acreqTxId} =
        hang 2 $ vsep
            [ "Slot:" <+> pretty acreqSlot
            , "Address:" <+> pretty acreqAddress
            , "TxId:" <+> pretty acreqTxId
            ]

{-| Wait for the next transaction that changes an address. The meaning of
    "next transaction" for an 'AddressChangeRequest' depends on the value
    of 'acreqTxId'.

    1. If 'acreqTxId' is 'Just txid' then @b@ is the next transaction if
    @b@ spends or produces an output at the given address and @b@ is the first
    transaction to be added to the ledger in or after 'acreqSlot' and
    after 'txid'.
    2. If 'acreqTxId' is 'Nothing' then @b@ is the next transaction if
    @b@ spends or produces an output at the given address and b is the first
    transaction to be added to the ledger in or after 'acreqSlot'.

    Some implications of this definition are:

    * If the transaction 'txid' is never added to the ledger then (1) will
    never return
    * If the slot 'acreqSlot' contains more than one transaction at the address
    then only (1) will ever return transactions other than the first one.

    To get all transactions that modify the address in a slot, it is prudent to
    call 'addressChangeRequest' repeatedly, using the ID of the last
    transaction that was returned
-}
addressChangeRequest ::
    forall s e.
    ( HasWatchAddress s
    , AsContractError e
    )
    => AddressChangeRequest
    -> Contract s e AddressChangeResponse
addressChangeRequest rq =
    let check :: AddressChangeResponse -> Maybe AddressChangeResponse
        check r@AddressChangeResponse{acrAddress, acrSlot}
                | acrAddress == acreqAddress rq && acrSlot >= acreqSlot rq = Just r
                | otherwise = Nothing
    in requestMaybe @AddressSymbol @_ @_ @s rq check

-- | Wait for the next transaction that changes an address.
nextTransactionAt ::
    forall s e.
    ( HasWatchAddress s
    , AsContractError e
    , HasAwaitSlot s
    )
    => Address
    -> Contract s e Tx
nextTransactionAt addr = do
    sl <- currentSlot
    acrTx <$> addressChangeRequest AddressChangeRequest{acreqSlot = sl, acreqTxId=Nothing, acreqAddress=addr}

-- | Watch an address for changes, and return the outputs
--   at that address when the total value at the address
--   has surpassed the given value.
fundsAtAddressGt
    :: forall s e.
       ( HasWatchAddress s
       , AsContractError e
       , HasAwaitSlot s
       , HasUtxoAt s
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
       , HasAwaitSlot s
       , HasUtxoAt s
       )
    => (Value -> Bool)
    -> Address
    -> Contract s e UtxoMap
fundsAtAddressCondition condition addr = loopM go () where
    go () = do
        cur <- utxoAt addr
        let presentVal = foldMap (txOutValue . txOutTxOut) cur
        if condition presentVal
            then pure (Right cur)
            else nextTransactionAt @s addr >> pure (Left ())

-- | Watch an address for changes, and return the outputs
--   at that address when the total value at the address
--   has reached or surpassed the given value.
fundsAtAddressGeq
    :: forall s e.
       ( HasWatchAddress s
       , AsContractError e
       , HasAwaitSlot s
       , HasUtxoAt s
       )
    => Address
    -> Value
    -> Contract s e UtxoMap
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
    let mkEvent addr = AddressChangeResponse{acrAddress=addr,acrSlot=sl,acrTx=tx}
    in Map.fromSet
        (Event . IsJust (Label @AddressSymbol) . mkEvent)
        (AM.addressesTouched utxo tx)

watchedAddress
    :: forall s.
    ( HasType AddressSymbol AddressChangeRequest (Output s))
    => Handlers s
    -> Maybe Address
watchedAddress (Handlers r) = acreqAddress <$> (trial' r (Label @AddressSymbol))
