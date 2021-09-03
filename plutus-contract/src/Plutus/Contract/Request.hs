{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
module Plutus.Contract.Request(
    -- * PAB requests
    -- ** Waiting
    awaitSlot
    , isSlot
    , currentSlot
    , waitNSlots
    , awaitTime
    , isTime
    , currentTime
    , waitNMilliSeconds
    -- ** Chain index queries
    , datumFromHash
    , validatorFromHash
    , mintingPolicyFromHash
    , stakeValidatorFromHash
    , redeemerFromHash
    , txOutFromRef
    , txFromTxId
    , utxoRefMembership
    , utxosAt
    , utxosTxOutTxAt
    , utxosTxOutTxFromTx
    , getTip
    -- ** Waiting for changes to the UTXO set
    , fundsAtAddressGt
    , fundsAtAddressGeq
    , fundsAtAddressCondition
    , watchAddressUntilSlot
    , watchAddressUntilTime
    , awaitUtxoSpent
    , utxoIsSpent
    , awaitUtxoProduced
    , utxoIsProduced
    -- ** Tx confirmation
    , TxStatus(..)
    , awaitTxStatusChange
    , awaitTxConfirmed
    , isTxConfirmed
    -- ** Contract instances
    , ownInstanceId
    -- ** Exposing endpoints
    , HasEndpoint
    , EndpointDescription(..)
    , Endpoint
    , endpoint
    , handleEndpoint
    , endpointWithMeta
    , endpointDescription
    , endpointReq
    , endpointResp
    -- ** Public keys
    , ownPubKey
    -- ** Submitting transactions
    , submitUnbalancedTx
    , submitBalancedTx
    , balanceTx
    , submitTx
    , submitTxConstraints
    , submitTxConstraintsSpending
    , submitTxConstraintsWith
    , submitTxConfirmed
    , mkTxConstraints
    -- * Etc.
    , ContractRow
    , pabReq
    ) where

import           Control.Lens                (Prism', preview, review, view)
import qualified Control.Monad.Freer.Error   as E
import           Data.Aeson                  (FromJSON, ToJSON)
import qualified Data.Aeson                  as JSON
import qualified Data.Aeson.Types            as JSON
import           Data.List.NonEmpty          (NonEmpty)
import           Data.Map                    (Map)
import qualified Data.Map                    as Map
import           Data.Maybe                  (catMaybes, mapMaybe)
import           Data.Proxy                  (Proxy (..))
import           Data.Row
import qualified Data.Text                   as Text
import           Data.Text.Extras            (tshow)
import           Data.Void                   (Void)
import           GHC.Natural                 (Natural)
import           GHC.TypeLits                (Symbol, symbolVal)
import           Ledger                      (Address, Datum, DatumHash, DiffMilliSeconds, MintingPolicy,
                                              MintingPolicyHash, POSIXTime, PubKey, Redeemer, RedeemerHash, Slot,
                                              StakeValidator, StakeValidatorHash, Tx, TxId, TxOutRef (txOutRefId),
                                              Validator, ValidatorHash, Value, addressCredential, fromMilliSeconds,
                                              txId)
import           Ledger.Constraints          (TxConstraints)
import           Ledger.Constraints.OffChain (ScriptLookups, UnbalancedTx)
import qualified Ledger.Constraints.OffChain as Constraints
import           Ledger.Tx                   (ChainIndexTxOut, ciTxOutValue)
import           Ledger.Typed.Scripts        (TypedValidator, ValidatorTypes (..))
import qualified Ledger.Value                as V
import           Plutus.Contract.Util        (loopM)
import qualified PlutusTx

import           Plutus.Contract.Effects     (ActiveEndpoint (..), PABReq (..), PABResp (..))
import qualified Plutus.Contract.Effects     as E
import           Plutus.Contract.Schema      (Input, Output)
import           Wallet.Types                (ContractInstanceId, EndpointDescription (..), EndpointValue (..))

import           Plutus.ChainIndex           (ChainIndexTx, Page (pageItems), txOutRefs)
import           Plutus.ChainIndex.Types     (Tip, TxStatus (..))
import           Plutus.Contract.Resumable
import           Plutus.Contract.Types

-- | Constraints on the contract schema, ensuring that the labels of the schema
--   are unique.
type ContractRow s =
  ( AllUniqueLabels (Input s)
  , AllUniqueLabels (Output s)
  )

{- Send a 'PABReq' and return the appropriate 'PABResp'
-}
pabReq ::
  forall w s e a.
  ( AsContractError e
  )
  => PABReq -- ^ The request to send
  -> Prism' PABResp a -- ^ Prism for the response
  -> Contract w s e a
pabReq req prism = Contract $ do
  x <- prompt @PABResp @PABReq req
  case preview prism x of
    Just r -> pure r
    _      -> E.throwError @e $ review _ResumableError $ WrongVariantError $ "unexpected answer: " <> tshow x

-- | Wait until the slot
awaitSlot ::
    forall w s e.
    ( AsContractError e
    )
    => Slot
    -> Contract w s e Slot
awaitSlot s = pabReq (AwaitSlotReq s) E._AwaitSlotResp

-- | Wait until the slot
isSlot ::
    forall w s e.
    ( AsContractError e
    )
    => Slot
    -> Promise w s e Slot
isSlot = Promise . awaitSlot

-- | Get the current slot number
currentSlot ::
    forall w s e.
    ( AsContractError e
    )
    => Contract w s e Slot
currentSlot = pabReq CurrentSlotReq E._CurrentSlotResp

-- | Wait for a number of slots to pass
waitNSlots ::
  forall w s e.
  ( AsContractError e
  )
  => Natural
  -> Contract w s e Slot
waitNSlots n = do
  c <- currentSlot
  awaitSlot $ c + fromIntegral n

-- | Wait until the slot where the given time falls into and return latest time
-- we know has passed.
--
-- Example: if starting time is 0 and slot length is 3s, then `awaitTime 4`
-- waits until slot 2 and returns the value `POSIXTime 5`.
awaitTime ::
    forall w s e.
    ( AsContractError e
    )
    => POSIXTime
    -> Contract w s e POSIXTime
awaitTime s = pabReq (AwaitTimeReq s) E._AwaitTimeResp

-- | Wait until the slot where the given time falls into and return latest time
-- we know has passed.
isTime ::
    forall w s e.
    ( AsContractError e
    )
    => POSIXTime
    -> Promise w s e POSIXTime
isTime = Promise . awaitTime

-- | Get the latest time of the current slot.
--
-- Example: if slot length is 3s and current slot is 2, then `currentTime`
-- returns the value `POSIXTime 5`
currentTime ::
    forall w s e.
    ( AsContractError e
    )
    => Contract w s e POSIXTime
currentTime = pabReq CurrentTimeReq E._CurrentTimeResp

-- | Wait for a number of milliseconds starting at the ending time of the current
-- slot, and return the latest time we know has passed.
--
-- Example: if starting time is 0, slot length is 3000ms and current slot is 0, then
-- `waitNMilliSeconds 0` returns the value `POSIXTime 2000` and `waitNMilliSeconds 1000`
-- returns the value `POSIXTime 5`.
waitNMilliSeconds ::
  forall w s e.
  ( AsContractError e
  )
  => DiffMilliSeconds
  -> Contract w s e POSIXTime
waitNMilliSeconds n = do
  t <- currentTime
  awaitTime $ t + fromMilliSeconds n

datumFromHash ::
    forall w s e.
    ( AsContractError e
    )
    => DatumHash
    -> Contract w s e (Maybe Datum)
datumFromHash h = do
  cir <- pabReq (ChainIndexQueryReq $ E.DatumFromHash h) E._ChainIndexQueryResp
  case cir of
    E.DatumHashResponse r -> pure r
    _ -> throwError $ review _OtherError
                    $ Text.pack "Could not request DatumFromHash from the chain index"

validatorFromHash ::
    forall w s e.
    ( AsContractError e
    )
    => ValidatorHash
    -> Contract w s e (Maybe Validator)
validatorFromHash h = do
  cir <- pabReq (ChainIndexQueryReq $ E.ValidatorFromHash h) E._ChainIndexQueryResp
  case cir of
    E.ValidatorHashResponse r -> pure r
    _ -> throwError $ review _OtherError
                    $ Text.pack "Could not request ValidatorFromHash from the chain index"

mintingPolicyFromHash ::
    forall w s e.
    ( AsContractError e
    )
    => MintingPolicyHash
    -> Contract w s e (Maybe MintingPolicy)
mintingPolicyFromHash h = do
  cir <- pabReq (ChainIndexQueryReq $ E.MintingPolicyFromHash h) E._ChainIndexQueryResp
  case cir of
    E.MintingPolicyHashResponse r -> pure r
    _ -> throwError $ review _OtherError
                    $ Text.pack "Could not request MintingPolicyFromHash from the chain index"

stakeValidatorFromHash ::
    forall w s e.
    ( AsContractError e
    )
    => StakeValidatorHash
    -> Contract w s e (Maybe StakeValidator)
stakeValidatorFromHash h = do
  cir <- pabReq (ChainIndexQueryReq $ E.StakeValidatorFromHash h) E._ChainIndexQueryResp
  case cir of
    E.StakeValidatorHashResponse r -> pure r
    _ -> throwError $ review _OtherError
                    $ Text.pack "Could not request StakeValidatorFromHash from the chain index"

redeemerFromHash ::
    forall w s e.
    ( AsContractError e
    )
    => RedeemerHash
    -> Contract w s e (Maybe Redeemer)
redeemerFromHash h = do
  cir <- pabReq (ChainIndexQueryReq $ E.RedeemerFromHash h) E._ChainIndexQueryResp
  case cir of
    E.RedeemerHashResponse r -> pure r
    _ -> throwError $ review _OtherError
                    $ Text.pack "Could not request RedeemerFromHash from the chain index"

txOutFromRef ::
    forall w s e.
    ( AsContractError e
    )
    => TxOutRef
    -> Contract w s e (Maybe ChainIndexTxOut)
txOutFromRef ref = do
  cir <- pabReq (ChainIndexQueryReq $ E.TxOutFromRef ref) E._ChainIndexQueryResp
  case cir of
    E.TxOutRefResponse r -> pure r
    _ -> throwError $ review _OtherError
                    $ Text.pack "Could not request TxOutFromRef from the chain index"

txFromTxId ::
    forall w s e.
    ( AsContractError e
    )
    => TxId
    -> Contract w s e (Maybe ChainIndexTx)
txFromTxId txid = do
  cir <- pabReq (ChainIndexQueryReq $ E.TxFromTxId txid) E._ChainIndexQueryResp
  case cir of
    E.TxIdResponse r -> pure r
    _ -> throwError $ review _OtherError
                    $ Text.pack "Could not request TxFromTxId from the chain index"

utxoRefMembership ::
    forall w s e.
    ( AsContractError e
    )
    => TxOutRef
    -> Contract w s e (Tip, Bool)
utxoRefMembership ref = do
  cir <- pabReq (ChainIndexQueryReq $ E.UtxoSetMembership ref) E._ChainIndexQueryResp
  case cir of
    E.UtxoSetMembershipResponse r -> pure r
    _ -> throwError $ review _OtherError
                    $ Text.pack "Could not request UtxoSetMembership from the chain index"

-- | Get the unspent transaction output references at an address.
utxoRefsAt ::
    forall w s e.
    ( AsContractError e
    )
    => Address
    -> Contract w s e (Tip, Page TxOutRef)
utxoRefsAt addr = do
  cir <- pabReq (ChainIndexQueryReq $ E.UtxoSetAtAddress $ addressCredential addr) E._ChainIndexQueryResp
  case cir of
    E.UtxoSetAtResponse r -> pure r
    _ -> throwError $ review _OtherError
                    $ Text.pack "Could not request UtxoSetAtAddress from the chain index"

-- | Get the unspent transaction outputs at an address.
utxosAt ::
    forall w s e.
    ( AsContractError e
    )
    => Address
    -> Contract w s e (Map TxOutRef ChainIndexTxOut)
utxosAt addr = do
  utxoRefs <- fmap (pageItems . snd) $ utxoRefsAt addr
  txOuts <- traverse txOutFromRef utxoRefs
  pure $ Map.fromList
       $ mapMaybe (\(ref, txOut) -> fmap (ref,) txOut)
       $ zip utxoRefs txOuts

-- | Get unspent transaction outputs with transaction from address.
utxosTxOutTxAt ::
    forall w s e.
    ( AsContractError e
    )
    => Address
    -> Contract w s e (Map TxOutRef (ChainIndexTxOut, ChainIndexTx))
utxosTxOutTxAt addr = do
  utxoRefs <- fmap (pageItems . snd) $ utxoRefsAt addr
  go mempty mempty utxoRefs
  where
    go :: Map TxId ChainIndexTx
       -> Map TxOutRef (ChainIndexTxOut, ChainIndexTx)
       -> [TxOutRef]
       -> Contract w s e (Map TxOutRef (ChainIndexTxOut, ChainIndexTx))
    go _ oldResult [] = pure oldResult
    go lookupTx oldResult (ref:refs) = do
      outM <- txOutFromRef ref
      case outM of
        Just out -> do
          let txid = txOutRefId ref
          -- Lookup the txid in the lookup table. If it's present, we don't need
          -- to query the chain index again. If it's not, we query the chain
          -- index and store the result in the lookup table.
          case Map.lookup txid lookupTx of
            Just tx -> do
              let result = oldResult <> Map.singleton ref (out, tx)
              go lookupTx result refs
            Nothing -> do
              -- We query the chain index for the tx and store it in the lookup
              -- table if it is found.
              txM <- txFromTxId txid
              case txM of
                Just tx -> do
                  let newLookupTx = lookupTx <> Map.singleton txid tx
                  let result = oldResult <> Map.singleton ref (out, tx)
                  go newLookupTx result refs
                Nothing ->
                  go lookupTx oldResult refs
        Nothing -> go lookupTx oldResult refs

-- | Get the unspent transaction outputs from a 'ChainIndexTx'.
utxosTxOutTxFromTx ::
    AsContractError e
    => ChainIndexTx
    -> Contract w s e [(TxOutRef, (ChainIndexTxOut, ChainIndexTx))]
utxosTxOutTxFromTx tx =
  catMaybes <$> mapM mkOutRef (txOutRefs tx)
  where
    mkOutRef txOutRef = do
      ciTxOutM <- txOutFromRef txOutRef
      pure $ ciTxOutM >>= \ciTxOut -> pure (txOutRef, (ciTxOut, tx))

getTip ::
    forall w s e.
    ( AsContractError e
    )
    => Contract w s e Tip
getTip = do
  cir <- pabReq (ChainIndexQueryReq E.GetTip) E._ChainIndexQueryResp
  case cir of
    E.GetTipResponse r -> pure r
    _ -> throwError $ review _OtherError
                    $ Text.pack "Could not request GetTip from the chain index"

-- | Wait until the target slot and get the unspent transaction outputs at an
-- address.
watchAddressUntilSlot ::
    forall w s e.
    ( AsContractError e
    )
    => Address
    -> Slot
    -> Contract w s e (Map TxOutRef ChainIndexTxOut)
watchAddressUntilSlot a slot = awaitSlot slot >> utxosAt a

-- | Wait until the target time and get the unspent transaction outputs at an
-- address.
watchAddressUntilTime ::
    forall w s e.
    ( AsContractError e
    )
    => Address
    -> POSIXTime
    -> Contract w s e (Map TxOutRef ChainIndexTxOut)
watchAddressUntilTime a time = awaitTime time >> utxosAt a

{-| Wait until the UTXO has been spent, returning the transaction that spends it.
-}
awaitUtxoSpent ::
  forall w s e.
  ( AsContractError e
  )
  => TxOutRef
  -> Contract w s e ChainIndexTx
awaitUtxoSpent utxo = pabReq (AwaitUtxoSpentReq utxo) E._AwaitUtxoSpentResp

{-| Wait until the UTXO has been spent, returning the transaction that spends it.
-}
utxoIsSpent ::
  forall w s e.
  ( AsContractError e
  )
  => TxOutRef
  -> Promise w s e ChainIndexTx
utxoIsSpent = Promise . awaitUtxoSpent

{-| Wait until one or more unspent outputs are produced at an address.
-}
awaitUtxoProduced ::
  forall w s e .
  ( AsContractError e
  )
  => Address
  -> Contract w s e (NonEmpty ChainIndexTx)
awaitUtxoProduced address =
  pabReq (AwaitUtxoProducedReq address) E._AwaitUtxoProducedResp

{-| Wait until one or more unspent outputs are produced at an address.
-}
utxoIsProduced ::
  forall w s e .
  ( AsContractError e
  )
  => Address
  -> Promise w s e (NonEmpty ChainIndexTx)
utxoIsProduced = Promise . awaitUtxoProduced

-- | Watch an address for changes, and return the outputs
--   at that address when the total value at the address
--   has surpassed the given value.
fundsAtAddressGt
    :: forall w s e.
       ( AsContractError e
       )
    => Address
    -> Value
    -> Contract w s e (Map TxOutRef ChainIndexTxOut)
fundsAtAddressGt addr vl =
    fundsAtAddressCondition (\presentVal -> presentVal `V.gt` vl) addr

fundsAtAddressCondition
    :: forall w s e.
       ( AsContractError e
       )
    => (Value -> Bool)
    -> Address
    -> Contract w s e (Map TxOutRef ChainIndexTxOut)
fundsAtAddressCondition condition addr = loopM go () where
    go () = do
        cur <- utxosAt addr
        let presentVal = foldMap (view ciTxOutValue) cur
        if condition presentVal
            then pure (Right cur)
            else awaitUtxoProduced addr >> pure (Left ())

-- | Watch an address for changes, and return the outputs
--   at that address when the total value at the address
--   has reached or surpassed the given value.
fundsAtAddressGeq
    :: forall w s e.
       ( AsContractError e
       )
    => Address
    -> Value
    -> Contract w s e (Map TxOutRef ChainIndexTxOut)
fundsAtAddressGeq addr vl =
    fundsAtAddressCondition (\presentVal -> presentVal `V.geq` vl) addr

-- | Wait for the status of a transaction to change
awaitTxStatusChange :: forall w s e. AsContractError e => TxId -> Contract w s e TxStatus
awaitTxStatusChange i = pabReq (AwaitTxStatusChangeReq i) (E._AwaitTxStatusChangeResp' i)

-- TODO: Configurable level of confirmation (for example, as soon as the tx is
--       included in a block, or only when it can't be rolled back anymore)
-- | Wait until a transaction is confirmed (added to the ledger).
--   If the transaction is never added to the ledger then 'awaitTxConfirmed' never
--   returns
awaitTxConfirmed :: forall w s e. (AsContractError e) => TxId -> Contract w s e ()
awaitTxConfirmed i = go where
  go = do
    newStatus <- awaitTxStatusChange i
    case newStatus of
      Unknown -> go
      _       -> pure ()

-- | Wait until a transaction is confirmed (added to the ledger).
isTxConfirmed :: forall w s e. (AsContractError e) => TxId -> Promise w s e ()
isTxConfirmed = Promise . awaitTxConfirmed

-- | Get the 'ContractInstanceId' of this instance.
ownInstanceId :: forall w s e. (AsContractError e) => Contract w s e ContractInstanceId
ownInstanceId = pabReq OwnContractInstanceIdReq E._OwnContractInstanceIdResp

type HasEndpoint l a s =
  ( HasType l (EndpointValue a) (Input s)
  , HasType l ActiveEndpoint (Output s)
  , KnownSymbol l
  , ContractRow s
  )

type Endpoint l a = l .== (EndpointValue a, ActiveEndpoint)

endpointReq :: forall l a s.
    ( HasEndpoint l a s )
    => ActiveEndpoint
endpointReq =
    ActiveEndpoint
        { aeDescription = EndpointDescription $ symbolVal (Proxy @l)
        , aeMetadata    = Nothing
        }

endpointDesc :: forall (l :: Symbol). KnownSymbol l => EndpointDescription
endpointDesc = EndpointDescription $ symbolVal (Proxy @l)

endpointResp :: forall l a s. (HasEndpoint l a s, ToJSON a) => a -> PABResp
endpointResp = ExposeEndpointResp (endpointDesc @l) . EndpointValue . JSON.toJSON

-- | Expose an endpoint, return the data that was entered
endpoint
  :: forall l a w s e b.
     ( HasEndpoint l a s
     , AsContractError e
     , FromJSON a
     )
  => (a -> Contract w s e b) -> Promise w s e b
endpoint f = Promise $ do
    (_, endpointValue) <- pabReq (ExposeEndpointReq $ endpointReq @l @a @s) E._ExposeEndpointResp
    a <- decode endpointValue
    f a

decode :: forall a w s e. (FromJSON a, AsContractError e) => EndpointValue JSON.Value -> Contract w s e a
decode EndpointValue{unEndpointValue} =
    either (throwError . review _OtherError . Text.pack) pure
    $ JSON.parseEither JSON.parseJSON unEndpointValue

handleEndpoint
  :: forall l a w s e1 e2 b.
     ( HasEndpoint l a s
     , AsContractError e1
     , FromJSON a
     )
  => (Either e1 a -> Contract w s e2 b) -> Promise w s e2 b
handleEndpoint f = Promise $ do
  a <- runError $ do
      (_, endpointValue) <- pabReq (ExposeEndpointReq $ endpointReq @l @a @s) E._ExposeEndpointResp
      decode endpointValue
  f a

-- | Expose an endpoint with some metadata. Return the data that was entered.
endpointWithMeta
  :: forall l a w s e meta b.
     ( HasEndpoint l a s
     , AsContractError e
     , ToJSON meta
     , FromJSON a
     )
  => meta
  -> (a -> Contract w s e b)
  -> Promise w s e b
endpointWithMeta meta f = Promise $ do
    (_, endpointValue) <- pabReq (ExposeEndpointReq s) E._ExposeEndpointResp
    a <- decode endpointValue
    f a
    where
        s = ActiveEndpoint
                { aeDescription = endpointDesc @l
                , aeMetadata    = Just $ JSON.toJSON meta
                }

endpointDescription :: forall l. KnownSymbol l => Proxy l -> EndpointDescription
endpointDescription = EndpointDescription . symbolVal

-- | Get a public key belonging to the wallet that runs this contract.
--   * Any funds paid to this public key will be treated as the wallet's own
--     funds
--   * The wallet is able to sign transactions with the private key of this
--     public key, for example, if the public key is added to the
--     'requiredSignatures' field of 'Tx'.
--   * There is a 1-n relationship between wallets and public keys (although in
--     the mockchain n=1)
ownPubKey :: forall w s e. (AsContractError e) => Contract w s e PubKey
ownPubKey = pabReq OwnPublicKeyReq E._OwnPublicKeyResp

-- | Send an unbalanced transaction to be balanced and signed. Returns the ID
--    of the final transaction when the transaction was submitted. Throws an
--    error if balancing or signing failed.
submitUnbalancedTx :: forall w s e. (AsContractError e) => UnbalancedTx -> Contract w s e Tx
-- See Note [Injecting errors into the user's error type]
submitUnbalancedTx utx = do
  tx <- balanceTx utx
  submitBalancedTx tx

-- | Send an unbalanced transaction to be balanced. Returns the balanced transaction.
--    Throws an error if balancing failed.
balanceTx :: forall w s e. (AsContractError e) => UnbalancedTx -> Contract w s e Tx
-- See Note [Injecting errors into the user's error type]
balanceTx t =
  let req = pabReq (BalanceTxReq t) E._BalanceTxResp in
  req >>= either (throwError . review _WalletError) pure . view E.balanceTxResponse

-- | Send an balanced transaction to be signed. Returns the ID
--    of the final transaction when the transaction was submitted. Throws an
--    error if signing failed.
submitBalancedTx :: forall w s e. (AsContractError e) => Tx -> Contract w s e Tx
-- See Note [Injecting errors into the user's error type]
submitBalancedTx t =
  let req = pabReq (WriteBalancedTxReq t) E._WriteBalancedTxResp in
  req >>= either (throwError . review _WalletError) pure . view E.writeBalancedTxResponse

-- | Build a transaction that satisfies the constraints, then submit it to the
--   network. The constraints do not refer to any typed script inputs or
--   outputs.
submitTx :: forall w s e.
  ( AsContractError e
  )
  => TxConstraints Void Void
  -> Contract w s e Tx
submitTx = submitTxConstraintsWith @Void mempty

-- | Build a transaction that satisfies the constraints, then submit it to the
--   network. Using the current outputs at the contract address and the
--   contract's own public key to solve the constraints.
submitTxConstraints
  :: forall a w s e.
  ( PlutusTx.ToData (RedeemerType a)
  , PlutusTx.FromData (DatumType a)
  , PlutusTx.ToData (DatumType a)
  , AsContractError e
  )
  => TypedValidator a
  -> TxConstraints (RedeemerType a) (DatumType a)
  -> Contract w s e Tx
submitTxConstraints inst = submitTxConstraintsWith (Constraints.typedValidatorLookups inst)

-- | Build a transaction that satisfies the constraints using the UTXO map
--   to resolve any input constraints (see 'Ledger.Constraints.TxConstraints.InputConstraint')
submitTxConstraintsSpending
  :: forall a w s e.
  ( PlutusTx.ToData (RedeemerType a)
  , PlutusTx.FromData (DatumType a)
  , PlutusTx.ToData (DatumType a)
  , AsContractError e
  )
  => TypedValidator a
  -> Map TxOutRef ChainIndexTxOut
  -> TxConstraints (RedeemerType a) (DatumType a)
  -> Contract w s e Tx
submitTxConstraintsSpending inst utxo =
  let lookups = Constraints.typedValidatorLookups inst <> Constraints.unspentOutputs utxo
  in submitTxConstraintsWith lookups

-- | Build a transaction that satisfies the constraints
mkTxConstraints :: forall a w s e.
  ( PlutusTx.ToData (RedeemerType a)
  , PlutusTx.FromData (DatumType a)
  , PlutusTx.ToData (DatumType a)
  , AsContractError e
  )
  => ScriptLookups a
  -> TxConstraints (RedeemerType a) (DatumType a)
  -> Contract w s e UnbalancedTx
mkTxConstraints sl constraints =
  either (throwError . review _ConstraintResolutionError) pure (Constraints.mkTx sl constraints)

-- | Build a transaction that satisfies the constraints, then submit it to the
--   network. Using the given constraints.
submitTxConstraintsWith
  :: forall a w s e.
  ( PlutusTx.ToData (RedeemerType a)
  , PlutusTx.FromData (DatumType a)
  , PlutusTx.ToData (DatumType a)
  , AsContractError e
  )
  => ScriptLookups a
  -> TxConstraints (RedeemerType a) (DatumType a)
  -> Contract w s e Tx
submitTxConstraintsWith sl constraints = mkTxConstraints sl constraints >>= submitUnbalancedTx

-- | A version of 'submitTx' that waits until the transaction has been
--   confirmed on the ledger before returning.
submitTxConfirmed :: forall w s e. (AsContractError e) => UnbalancedTx -> Contract w s e ()
submitTxConfirmed t = submitUnbalancedTx t >>= awaitTxConfirmed . txId
