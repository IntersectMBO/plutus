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
import           Ledger                                     (Address, Slot, Value, txId)
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
--   an address in a slot.
data AddressChangeResponse =
    AddressChangeResponse
        { acrAddress :: Address -- ^ The address
        , acrSlot    :: Slot -- ^ The slot
        , acrTxns    :: [Tx] -- ^ Transactions that were validated in the slot and spent or produced at least one output at the address.
        }
        deriving stock (Eq, Generic, Show)
        deriving anyclass (ToJSON, FromJSON)

instance Pretty AddressChangeResponse where
    pretty AddressChangeResponse{acrAddress, acrTxns, acrSlot} =
        hang 2 $ vsep
            [ "Address:" <+> pretty acrAddress
            , "Slot:" <+> pretty acrSlot
            , "Tx IDs:" <+> pretty (txId <$> acrTxns)
            ]

-- | Request for information about transactions that spend or produce
--   outputs at a specific address in a slot.
data AddressChangeRequest =
    AddressChangeRequest
        { acreqSlot    :: Slot -- ^ The slot
        , acreqAddress :: Address -- ^ The address
        }
        deriving stock (Eq, Generic, Show, Ord)
        deriving anyclass (ToJSON, FromJSON)

instance Pretty AddressChangeRequest where
    pretty AddressChangeRequest{acreqSlot, acreqAddress} =
        hang 2 $ vsep
            [ "Slot:" <+> pretty acreqSlot
            , "Address:" <+> pretty acreqAddress
            ]

{-| Get the transactions that modified an address in a specific slot.
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

-- | Call 'addresssChangeRequest' for the address in each slot, until at least one
--   transaction is returned that modifies the address.
nextTransactionsAt ::
    forall s e.
    ( HasWatchAddress s
    , AsContractError e
    , HasAwaitSlot s
    )
    => Address
    -> Contract s e [Tx]
nextTransactionsAt addr = do
    initial <- currentSlot
    let go sl = do
            txns <- acrTxns <$> addressChangeRequest AddressChangeRequest{acreqSlot = sl, acreqAddress=addr}
            if null txns
                then go (succ sl)
                else pure txns
    go initial

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
            else nextTransactionsAt @s addr >> pure (Left ())

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
    let mkEvent addr = AddressChangeResponse{acrAddress=addr,acrSlot=sl,acrTxns=[tx]}
    in Map.fromSet
        (Event . IsJust (Label @AddressSymbol) . mkEvent)
        (AM.addressesTouched utxo tx)

watchedAddress
    :: forall s.
    ( HasType AddressSymbol AddressChangeRequest (Output s))
    => Handlers s
    -> Maybe Address
watchedAddress (Handlers r) = acreqAddress <$> (trial' r (Label @AddressSymbol))
