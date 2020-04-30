{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
module Plutus.SCB.Core.ContractInstance(
    lookupContractState
    , processFirstInboxMessage
    , processAllContractInboxes
    , lookupContract
    , activateContract
    -- * Contract outboxes
    , processAllContractOutboxes
    , processOwnPubkeyRequests
    , processAwaitSlotRequests
    , processUtxoAtRequests
    , processWriteTxRequests
    -- * Calling an endpoint
    , callContractEndpoint
    ) where

import           Control.Lens
import           Control.Monad                                     (unless, void)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error                         (Error, runError, throwError)
import           Control.Monad.Freer.Extra.Log
import qualified Data.Aeson                                        as JSON
import           Data.Foldable                                     (fold, traverse_)
import qualified Data.Map                                          as Map
import           Data.Semigroup                                    (Last (..))
import           Data.Sequence                                     (Seq)
import qualified Data.Sequence                                     as Seq
import qualified Data.Set                                          as Set
import qualified Data.Text                                         as Text
import           Data.Text.Prettyprint.Doc                         (Pretty, pretty, (<+>))

import           Language.Plutus.Contract.Effects.AwaitSlot        (WaitingForSlot (..))
import           Language.Plutus.Contract.Effects.AwaitTxConfirmed (TxConfirmed (..), TxIdSet (..))
import           Language.Plutus.Contract.Effects.ExposeEndpoint   (ActiveEndpoints (..), EndpointDescription (..),
                                                                    EndpointValue (..))
import           Language.Plutus.Contract.Effects.UtxoAt           (UtxoAtAddress (..))
import           Language.Plutus.Contract.Effects.WatchAddress     (AddressSet (..))
import           Language.Plutus.Contract.Effects.WriteTx          (PendingTransactions (..), WriteTxResponse (..))
import           Language.Plutus.Contract.Wallet                   (balanceWallet)

import qualified Ledger
import           Ledger.AddressMap                                 (AddressMap)
import qualified Ledger.AddressMap                                 as AM
import           Ledger.Constraints.OffChain                       (UnbalancedTx (..))
import           Ledger.Slot                                       (Slot)
import           Wallet.API                                        (signWithOwnPublicKey)
import           Wallet.Effects                                    (ChainIndexEffect, SigningProcessEffect,
                                                                    WalletEffect, ownPubKey, startWatching, submitTxn,
                                                                    transactionConfirmed, walletSlot, watchedAddresses)

import           Plutus.SCB.Command                                (saveBalancedTx, saveBalancedTxResult,
                                                                    saveContractState, sendContractEvent)
import           Plutus.SCB.Effects.Contract                       (ContractCommand (..), ContractEffect)
import qualified Plutus.SCB.Effects.Contract                       as Contract
import           Plutus.SCB.Effects.EventLog                       (EventLogEffect, runCommand, runGlobalQuery)
import           Plutus.SCB.Effects.UUID                           (UUIDEffect, uuidNextRandom)
import           Plutus.SCB.Events                                 (ChainEvent (..))
import           Plutus.SCB.Events.Contract                        (ContractEvent (..), ContractInstanceId (..),
                                                                    ContractInstanceState (..), ContractIteration (..),
                                                                    ContractMailbox (..), ContractRequest (..),
                                                                    ContractResponse (..), MailboxMessage (..),
                                                                    PartiallyDecodedResponse (..), iterationZero)
import qualified Plutus.SCB.Query                                  as Query
import           Plutus.SCB.Types                                  (SCBError (..), Source (ContractEventSource, NodeEventSource, UserEventSource, WalletEventSource))
import           Plutus.SCB.Utils                                  (render, tshow)

import qualified Plutus.SCB.Core.Projections                       as Projections

sendContractStateMessages ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        , Member (Error SCBError) effs
        , Member Log effs
        )
    => t
    -> ContractInstanceId
    -> ContractIteration
    -> PartiallyDecodedResponse
    -> Eff effs ()
sendContractStateMessages t instanceID iteration newState = do
    logInfo . render $ "Sending messages for contract" <+> pretty instanceID <+> "at iteration" <+> pretty iteration
    let is = ContractInstanceState
            { csContract = instanceID
            , csCurrentIteration = iteration
            , csCurrentState = newState
            , csContractDefinition = t
            }
    void
        $ runCommand (sendContractEvent @t) ContractEventSource
        $ ContractInstanceStateUpdateEvent is

    void $ runCommand (saveContractState @t) UserEventSource is

    decodedRequests <- Contract.decodeContractRequests newState
    logInfo . render $ "There are" <+> pretty (length decodedRequests) <+> "requests for this contract"
    traverse_ (sendContractOutboxMessage @t instanceID iteration) decodedRequests

sendContractMessage ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        )
    => ContractInstanceId
    -> ContractIteration
    -> MailboxMessage
    -> Eff effs [ChainEvent t]
sendContractMessage instanceID iteration =
    runCommand (sendContractEvent @t) ContractEventSource
    . ContractMailboxEvent ContractMailbox{cmInstance = instanceID, cmIteration = iteration}

sendContractOutboxMessage ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        )
    => ContractInstanceId
    -> ContractIteration
    -> ContractRequest
    -> Eff effs [ChainEvent t]
sendContractOutboxMessage instanceID iteration =
    sendContractMessage instanceID iteration . OutboxMessage

sendContractInboxMessage ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    )
    => ContractInstanceId
    -> ContractIteration
    -> ContractResponse
    -> Eff effs [ChainEvent t]
sendContractInboxMessage i it =
    sendContractMessage i it . InboxMessage

-- | Get the current state of the contract instance
lookupContractState ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member (Error SCBError) effs
    )
    => ContractInstanceId
    -> Eff effs (ContractInstanceState t)
lookupContractState instanceID = do
    mp <- runGlobalQuery (Query.contractState @t)
    case Map.lookup instanceID mp of
        Nothing       -> throwError $ OtherError $ "Contract instance not found " <> tshow instanceID
        Just (Last s) -> pure s

-- | For a given contract instance, take the first message
--   from the inbox and update the contract with it.
processFirstInboxMessage ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        , Member (ContractEffect t) effs
        , Member (Error SCBError) effs
        , Member Log effs
        )
    => ContractInstanceId
    -> Seq ContractResponse
    -> Eff effs ()
processFirstInboxMessage instanceID messages = do
    logInfo $ "processFirstInboxMessage start for " <> render (pretty instanceID)
    case Seq.viewl messages of
        msg Seq.:< _ -> do
            logInfo . render $ "The first message is: " <+> pretty msg
            logInfo "Looking up the contract."
            -- look up contract 't'
            ContractInstanceState{csCurrentIteration, csCurrentState, csContractDefinition} <- lookupContractState @t instanceID
            -- process the message
            let payload = Contract.contractMessageToPayload msg
            newState <- Contract.invokeContractUpdate_ csContractDefinition csCurrentState payload

            -- send out the new requests
            -- see note [Contract Iterations]
            let newIteration = succ csCurrentIteration
            sendContractStateMessages csContractDefinition instanceID newIteration newState
            logInfo . render $ "Updated contract" <+> pretty instanceID <+> "to new iteration" <+> pretty newIteration
        _ -> logInfo "No messages."
    logInfo "processFirstInboxMessage end"

-- | Check the inboxes of all contracts.
processAllContractInboxes ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        , Member (ContractEffect t) effs
        , Member (Error SCBError) effs
        , Member Log effs
        )
    => Eff effs ()
processAllContractInboxes = do
    logInfo "processAllContractInboxes start"
    state <- Query.contractStates <$> runGlobalQuery (Query.inboxMessages @t)
    itraverse_ (\cid (_, rsp) -> processFirstInboxMessage @t cid rsp) state
    logInfo "processAllContractInboxes end"

-- | Generic error message for failures during the contract lookup
newtype ContractLookupError = ContractLookupError { unContractLookupError :: String }

lookupContract ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Show t
    , Ord t
    )
    => t
    -> Eff effs (Either ContractLookupError t)
lookupContract t = do
    installed <- Projections.installedContracts
    let matchingContracts =
            Set.filter
                (\cp -> cp == t)
                installed
    pure
        $ maybe
            (Left (ContractLookupError (show t)))
            Right
            (Set.lookupMin matchingContracts)

-- | Create a new instance of the contract
activateContract ::
    forall t effs.
    ( Member Log effs
    , Member (EventLogEffect (ChainEvent t)) effs
    , Member (Error SCBError) effs
    , Member UUIDEffect effs
    , Member (ContractEffect t) effs
    , Show t
    , Pretty t
    , Ord t
    )
    => t
    -> Eff effs ContractInstanceId
activateContract contract = do
    logInfo . render $ "Finding contract" <+> pretty contract
    contractDef <-
        either (throwError . ContractNotFound . unContractLookupError) pure =<<
        lookupContract @t contract
    activeContractInstanceId <- ContractInstanceId <$> uuidNextRandom
    logInfo . render $ "Initializing contract instance with ID" <+> pretty activeContractInstanceId
    let currentIteration = iterationZero
    response <- Contract.invokeContract @t $ InitContract contractDef
    sendContractStateMessages @t contract activeContractInstanceId currentIteration response
    logInfo . render $ "Activated contract instance:" <+> pretty activeContractInstanceId
    pure activeContractInstanceId

processOwnPubkeyRequests ::
    forall t effs.
    ( Member Log effs
    , Member (EventLogEffect (ChainEvent t)) effs
    , Member WalletEffect effs
    )
    => Eff effs ()
processOwnPubkeyRequests = do
    logInfo "processOwnPubkeyRequests start"
    state <- Query.contractStates <$> runGlobalQuery (Query.ownPubKeyRequests @t)
    let go :: Ledger.PubKey -> ContractInstanceId -> (ContractIteration, ()) -> Eff effs [ChainEvent t]
        go pk i (it, ()) = do
            logDebug . render $ "processOwnPubkeyRequest" <+> pretty i <+> pretty pk
            sendContractInboxMessage @t i it (OwnPubkeyResponse pk)
    unless (Map.null state) $ do
        -- we only ask for the public key if there are actually any messages
        -- to process
        pk <- ownPubKey
        itraverse_ (go pk) state
    logInfo "processOwnPubkeyRequests end"

processAwaitSlotRequests ::
    forall t effs.
    ( Member Log effs
    , Member (EventLogEffect (ChainEvent t)) effs
    , Member WalletEffect effs
    )
    => Eff effs ()
processAwaitSlotRequests = do
    logInfo "processAwaitSlotRequests start"
    state <- Query.contractStates <$> runGlobalQuery (Query.awaitSlotRequests @t)
    unless (Map.null state) $ do
        -- we only ask for the wallet slot if there are actually any messages
        -- to process
        slot <- walletSlot
        itraverse_ (processAwaitSlotRequest @t slot) state
    logInfo "processAwaitSlotRequests end"

processAwaitSlotRequest ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member Log effs
    )
    => Slot
    -> ContractInstanceId
    -> (ContractIteration, WaitingForSlot)
    -> Eff effs [ChainEvent t]
processAwaitSlotRequest currentSlot i (it, WaitingForSlot (Just targetSlot))
    | currentSlot >= targetSlot = do
        logDebug . render $ "processAwaitSlotRequest" <+> pretty i <+> pretty targetSlot
        sendContractInboxMessage @t i it (AwaitSlotResponse currentSlot)
processAwaitSlotRequest _ _ _ = pure []

processUtxoAtRequests ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member ChainIndexEffect effs
    , Member Log effs
    )
    => Eff effs ()
processUtxoAtRequests = do
    logInfo "processUtxoAtRequests start"
    state <- Query.contractStates <$> runGlobalQuery (Query.utxoAtRequests @t)
    unless (Map.null state) $ do
        -- we only ask for the utxo index if there are actually any messages
        -- to process
        utxos <- watchedAddresses
        itraverse_ (processUtxoAtRequest @t utxos) state
    logInfo "processUtxoAtRequests end"

processUtxoAtRequest ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member ChainIndexEffect effs
    , Member Log effs
    )
    => AddressMap
    -> ContractInstanceId
    -> (ContractIteration, AddressSet)
    -> Eff effs [ChainEvent t]
processUtxoAtRequest utxos i (it, AddressSet addresses) =
    let go :: Ledger.Address -> Eff effs [ChainEvent t]
        go address = do
            logDebug . render $ "processUtxoAtRequest" <+> pretty i <+> pretty address
            startWatching address
            let response = UtxoAtAddress
                    { address = address
                    , utxo    = view (AM.fundsAt address) utxos
                    }
            sendContractInboxMessage @t i it (UtxoAtResponse response)
    in fold <$> traverse go (Set.toList addresses)

processWriteTxRequests ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member ChainIndexEffect effs
    , Member WalletEffect effs
    , Member Log effs
    , Member SigningProcessEffect effs
    )
    => Eff effs ()
processWriteTxRequests = do
    logInfo "processWriteTxRequests start"
    state <- Query.contractStates <$> runGlobalQuery (Query.writeTxRequests @t)
    itraverse_ (processWriteTxRequest @t) state
    logInfo "processWriteTxRequests start"

processWriteTxRequest ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member Log effs
    , Member ChainIndexEffect effs
    , Member WalletEffect effs
    , Member SigningProcessEffect effs
    )
    => ContractInstanceId
    -> (ContractIteration, PendingTransactions)
    -> Eff effs [ChainEvent t]
processWriteTxRequest i (it, PendingTransactions txns) =
    let go :: UnbalancedTx -> Eff effs [ChainEvent t]
        go unbalancedTx = do
            logInfo "processWriteTxRequest"
            logInfo "Start watching contract addresses."
            wa <- watchedAddresses
            traverse_ startWatching (AM.addressesTouched wa (unBalancedTxTx unbalancedTx))
            logInfo $ "Balancing unbalanced TX: " <> tshow unbalancedTx
            r <- runError $ do
                    balancedTx <- balanceWallet unbalancedTx
                    signedTx <- signWithOwnPublicKey balancedTx
                    logInfo $ "Storing signed TX: " <> tshow signedTx
                    void $ runCommand (saveBalancedTx @t) WalletEventSource balancedTx
                    logInfo $ "Submitting signed TX: " <> tshow signedTx
                    balanceResult <- submitTx signedTx
                    void $ runCommand (saveBalancedTxResult @t) NodeEventSource balanceResult
                    pure balanceResult
            let response = either WriteTxFailed (WriteTxSuccess . Ledger.txId) r
            logInfo . render $ "processWriteTxRequest result:" <+> pretty response
            sendContractInboxMessage i it (WriteTxResponse response)
    in fold <$> traverse go txns

-- | A wrapper around the NodeAPI function that returns some more
-- useful evidence of the work done.
submitTx :: (Member WalletEffect effs) => Ledger.Tx -> Eff effs Ledger.Tx
submitTx tx = submitTxn tx >> pure tx

processNextTxAtRequests ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member Log effs
    )
    => Eff effs ()
processNextTxAtRequests = do
    logInfo "processNextTxAtRequests start"
    state <- Query.contractStates <$> runGlobalQuery (Query.nextTxAtRequests @t)
    itraverse_ processNextTxAtRequest state
    logInfo "processNextTxAtRequests end"

processNextTxAtRequest ::
    forall effs.
    ( Member Log effs )
    => ContractInstanceId
    -> (ContractIteration, AddressSet)
    -> Eff effs ()
processNextTxAtRequest i (_, AddressSet addr) = do
    let go :: Ledger.Address -> Eff effs ()
        go address = do
            logDebug . render $ "processNextTxAtRequest" <+> pretty i <+> pretty address
    traverse_ go (Set.toList addr)

processTxConfirmedRequests ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member ChainIndexEffect effs
    , Member Log effs
    )
    => Eff effs ()
processTxConfirmedRequests = do
    logInfo "processTxConfirmedRequests start"
    state <- Query.contractStates <$> runGlobalQuery (Query.awaitTxConfirmedRequests @t)
    itraverse_ (processTxConfirmedRequest @t) state
    logInfo "processTxConfirmedRequests end"

processTxConfirmedRequest ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member ChainIndexEffect effs
    , Member Log effs
    )
    => ContractInstanceId
    -> (ContractIteration, TxIdSet)
    -> Eff effs [ChainEvent t]
processTxConfirmedRequest i (it, TxIdSet txids) =
    let go txid = do
            logDebug . render $ "processTxConfirmedRequest" <+> pretty i <+> pretty txid
            confirmed <- transactionConfirmed txid
            if confirmed
                then sendContractInboxMessage i it (AwaitTxConfirmedResponse $ TxConfirmed txid)
                else pure []
    in fold <$> traverse go (Set.toList txids)

-- | Look at the outboxes of all contract instances and process them.
processAllContractOutboxes ::
    forall t effs.
    ( Member Log effs
    , Member (EventLogEffect (ChainEvent t)) effs
    , Member WalletEffect effs
    , Member ChainIndexEffect effs
    , Member SigningProcessEffect effs
    )
    => Eff effs ()
processAllContractOutboxes = do
    logInfo "processAllContractOutboxes start"
    -- TODO: maybe this should be interleaved with 'processAllContractInboxes'
    --       to avoid doing too much work?
    processOwnPubkeyRequests @t
    processAwaitSlotRequests @t
    processUtxoAtRequests @t
    processWriteTxRequests @t
    processTxConfirmedRequests @t
    processNextTxAtRequests @t
    logInfo "processAllContractOutboxes end"

callContractEndpoint ::
    forall t a effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member Log effs
    , Member (Error SCBError) effs
    , JSON.ToJSON a
    )
    => ContractInstanceId
    -> String
    -> a
    -> Eff effs [ChainEvent t]
callContractEndpoint inst endpointName endpointValue = do
    logInfo . render $ "calling endpoint" <+> pretty endpointName <+> "on instance" <+> pretty inst
    state <- Query.contractStates <$> runGlobalQuery (Query.userEndpointRequests @t)
    (it, ActiveEndpoints activeEndpointNames) <-
        maybe
            (throwError (OtherError $ "Contract " <> Text.pack (show inst) <> " has not requested any user input"))
            pure
            (Map.lookup inst state)
    unless ((EndpointDescription endpointName) `Set.member` activeEndpointNames) $
        throwError (OtherError $ "Contract " <> Text.pack (show inst) <> " has not requested endpoint " <> Text.pack endpointName)

    sendContractInboxMessage @t inst it
        $ UserEndpointResponse (Text.pack endpointName) (EndpointValue $ JSON.toJSON endpointValue)

