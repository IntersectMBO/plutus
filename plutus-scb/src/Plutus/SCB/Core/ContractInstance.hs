{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
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
import           Control.Monad                                     (guard, void, when)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error                         (Error, runError, throwError)
import           Control.Monad.Freer.Extra.Log
import qualified Data.Aeson                                        as JSON
import           Data.Foldable                                     (traverse_)
import qualified Data.Map                                          as Map
import           Data.Maybe                                        (mapMaybe)
import           Data.Semigroup                                    (Last (..))
import qualified Data.Set                                          as Set
import qualified Data.Text                                         as Text
import           Data.Text.Prettyprint.Doc                         (Pretty, pretty, (<+>))

import           Language.Plutus.Contract.Effects.AwaitSlot        (WaitingForSlot (..))
import           Language.Plutus.Contract.Effects.AwaitTxConfirmed (TxConfirmed (..))
import           Language.Plutus.Contract.Effects.ExposeEndpoint   (ActiveEndpoint (..), EndpointDescription (..),
                                                                    EndpointValue (..))
import           Language.Plutus.Contract.Effects.UtxoAt           (UtxoAtAddress (..))
import           Language.Plutus.Contract.Effects.WriteTx          (WriteTxResponse (..))
import           Language.Plutus.Contract.Resumable                (Request (..), Response (..))
import           Language.Plutus.Contract.Trace.RequestHandler     (RequestHandler (..), extract, tryHandler,
                                                                    wrapHandler)
import           Language.Plutus.Contract.Wallet                   (balanceWallet)

import qualified Ledger
import qualified Ledger.AddressMap                                 as AM
import           Ledger.Constraints.OffChain                       (UnbalancedTx (..))
import           Wallet.API                                        (signWithOwnPublicKey)
import           Wallet.Effects                                    (AddressChangeRequest (..), ChainIndexEffect,
                                                                    SigningProcessEffect, WalletEffect, nextTx,
                                                                    ownPubKey, startWatching, submitTxn,
                                                                    transactionConfirmed, walletSlot, watchedAddresses)

import           Plutus.SCB.Command                                (saveBalancedTx, saveBalancedTxResult,
                                                                    saveContractState, sendContractEvent)
import           Plutus.SCB.Effects.Contract                       (ContractCommand (..), ContractEffect)
import qualified Plutus.SCB.Effects.Contract                       as Contract
import           Plutus.SCB.Effects.EventLog                       (EventLogEffect, runCommand, runGlobalQuery)
import           Plutus.SCB.Effects.UUID                           (UUIDEffect, uuidNextRandom)
import           Plutus.SCB.Events                                 (ChainEvent (..))
import           Plutus.SCB.Events.Contract                        (ContractEvent (..), ContractInstanceId (..),
                                                                    ContractInstanceState (..), ContractResponse (..),
                                                                    ContractSCBRequest (..), IterationID,
                                                                    PartiallyDecodedResponse (..),
                                                                    unContractHandlersResponse)
import qualified Plutus.SCB.Events.Contract                        as Events.Contract
import qualified Plutus.SCB.Query                                  as Query
import           Plutus.SCB.Types                                  (SCBError (..), Source (ContractEventSource, NodeEventSource, UserEventSource, WalletEventSource))
import           Plutus.SCB.Utils                                  (render, tshow)

import qualified Plutus.SCB.Core.Projections                       as Projections

sendContractStateMessages ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        , Member Log effs
        )
    => t
    -> ContractInstanceId
    -> IterationID
    -> PartiallyDecodedResponse ContractSCBRequest
    -> Eff effs ()
sendContractStateMessages t instanceID iteration newState = do
    logInfo . render $ "Sending messages for contract" <+> pretty instanceID <+> "at iteration" <+> pretty iteration
    logInfo . render $ "The contract has the following requests:" <+> pretty (fmap (\rq -> rq{rqRequest = ()}) $ hooks newState)
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

sendContractMessage ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        )
    => ContractInstanceId
    -> Response ContractResponse
    -> Eff effs [ChainEvent t]
sendContractMessage instanceID =
    runCommand (sendContractEvent @t) ContractEventSource
    . ContractInboxMessage instanceID

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
    -> Last (Response ContractResponse)
    -> Eff effs ()
processFirstInboxMessage instanceID (Last msg) = do
    logInfo $ "processFirstInboxMessage start for " <> render (pretty instanceID)
    logInfo . render $ "The first message is: " <+> pretty msg
    logInfo "Looking up the contract."
    -- look up contract 't'
    ContractInstanceState{csCurrentIteration, csCurrentState, csContractDefinition} <- lookupContractState @t instanceID
    when (csCurrentIteration == rspItID msg) $ do
        -- process the message
        let payload = Contract.contractMessageToPayload msg
        newState <- Contract.invokeContractUpdate_ csContractDefinition csCurrentState payload
        -- send out the new requests
        -- see note [Contract Iterations]
        let newIteration = succ csCurrentIteration
        sendContractStateMessages csContractDefinition instanceID newIteration newState
        logInfo . render $ "Updated contract" <+> pretty instanceID <+> "to new iteration" <+> pretty newIteration
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
    state <- runGlobalQuery (Query.inboxMessages @t)
    itraverse_ (processFirstInboxMessage @t) state
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
    let initialIteration = succ mempty -- FIXME get max it. from initial response
    response <- fmap (fmap unContractHandlersResponse) <$> Contract.invokeContract @t $ InitContract contractDef
    logInfo . render $ "Response was: " <+> pretty response
    sendContractStateMessages @t contract activeContractInstanceId initialIteration response
    logInfo . render $ "Activated contract instance:" <+> pretty activeContractInstanceId
    pure activeContractInstanceId

respondtoRequests ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member Log effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
    -> Eff effs ()
respondtoRequests handler = do
    contractStates <- runGlobalQuery (Query.contractState @t)
    let state = fmap (hooks . csCurrentState . getLast) contractStates
    itraverse_ (runRequestHandler @t handler) state

-- | Run a 'RequestHandler' on the 'ContractSCBRequest' list of a contract
--   instance and send the responses to the contract instance.
runRequestHandler ::
    forall t effs req.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member Log effs
    )
    => RequestHandler effs req ContractResponse
    -> ContractInstanceId
    -> [Request req]
    -> Eff effs [ChainEvent t]
runRequestHandler h contractInstance requests = do
    logDebug . render $ "runRequestHandler for" <+> pretty contractInstance <+> "with" <+> pretty (length requests) <+> "requests"
    logDebug . render . pretty . fmap (\req -> req{rqRequest = ()}) $ requests

    -- try the handler on the requests until it succeeds for the first time, then stop.
    -- We want to handle at most 1 request per iteration.
    (response :: Maybe (Response ContractResponse)) <-
        tryHandler (wrapHandler h) requests

    case response of
        Just rsp ->
            sendContractMessage @t contractInstance rsp
        _ -> do
            logDebug "runRequestHandler: did not handle any requests"
            pure []

processOwnPubkeyRequests ::
    forall effs.
    ( Member Log effs
    , Member WalletEffect effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
processOwnPubkeyRequests = RequestHandler $ \req -> do
        _ <- extract Events.Contract._OwnPubkeyRequest req
        logInfo "processOwnPubkeyRequests start"
        pk <- ownPubKey
        logInfo "processOwnPubkeyRequests end"
        pure (OwnPubkeyResponse pk)

processAwaitSlotRequests ::
    forall effs.
    ( Member Log effs
    , Member WalletEffect effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
processAwaitSlotRequests = RequestHandler $ \req -> do
    WaitingForSlot targetSlot <- extract Events.Contract._AwaitSlotRequest req
    logInfo "processAwaitSlotRequests start"
    currentSlot <- walletSlot
    logDebug . render $ "targetSlot:" <+> pretty targetSlot <+> "current slot:" <+> pretty currentSlot
    guard (targetSlot >= currentSlot)
    logInfo "processAwaitSlotRequests end"
    pure $ AwaitSlotResponse currentSlot

processUtxoAtRequests ::
    forall effs.
    ( Member ChainIndexEffect effs
    , Member Log effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
processUtxoAtRequests = RequestHandler $ \req -> do
    address <- extract Events.Contract._UtxoAtRequest req
    logDebug . render $ "processUtxoAtRequest" <+> pretty address
    utxos <- watchedAddresses
    startWatching address
    let response = UtxoAtAddress
            { address = address
            , utxo    = view (AM.fundsAt address) utxos
            }
    logInfo "processUtxoAtRequests end"
    pure $ UtxoAtResponse response

processWriteTxRequests ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member ChainIndexEffect effs
    , Member WalletEffect effs
    , Member Log effs
    , Member SigningProcessEffect effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
processWriteTxRequests = RequestHandler $ \req -> do
    -- logDebug . render $ "The request is a" <+> pretty req
    unbalancedTx <- extract Events.Contract._WriteTxRequest req
    logInfo "processWriteTxRequests start"
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
    let response = either WriteTxFailed WriteTxSuccess r
    logInfo . render $ "processWriteTxRequest result:" <+> pretty response
    logInfo "processWriteTxRequests end"
    pure (WriteTxResponse response)

-- | A wrapper around the NodeAPI function that returns some more
-- useful evidence of the work done.
submitTx :: (Member WalletEffect effs) => Ledger.Tx -> Eff effs Ledger.Tx
submitTx tx = submitTxn tx >> pure tx

processNextTxAtRequests ::
    forall effs.
    ( Member Log effs
    , Member WalletEffect effs
    , Member ChainIndexEffect effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
processNextTxAtRequests = RequestHandler $ \req -> do
    request <- extract Events.Contract._NextTxAtRequest req
    logInfo "processNextTxAtRequests start"
    logDebug . render $ "processNextTxAtRequest" <+> pretty request
    slot <- walletSlot
    guard $ slot > acreqSlot request
    response <- nextTx request
    logInfo "processNextTxAtRequests end"
    pure $ NextTxAtResponse response

processTxConfirmedRequests ::
    forall effs.
    ( Member ChainIndexEffect effs
    , Member Log effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
processTxConfirmedRequests = RequestHandler $ \req -> do
    txid <- extract Events.Contract._AwaitTxConfirmedRequest req
    logInfo "processTxConfirmedRequests start"
    logDebug . render $ "processTxConfirmedRequest" <+> pretty txid
    confirmed <- transactionConfirmed txid
    logDebug . render $ "confirmed" <+> pretty confirmed
    guard confirmed
    logInfo "processTxConfirmedRequests end"
    pure $ AwaitTxConfirmedResponse $ TxConfirmed txid

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
    -- we can't use respondtoRequests here because we want to call the endpoint only on
    -- the contract instance 'inst'. And we want to error if the endpoint is not active.
    logInfo . render $ "calling endpoint" <+> pretty endpointName <+> "on instance" <+> pretty inst
    state <- fmap (hooks . csCurrentState . getLast) <$> runGlobalQuery (Query.contractState @t)
    let activeEndpoints =
            filter ((==) (EndpointDescription endpointName) . unActiveEndpoints . rqRequest)
            $ mapMaybe (traverse (preview Events.Contract._UserEndpointRequest))
            $ Map.findWithDefault [] inst state

    when (null activeEndpoints) $
        throwError (OtherError $ "Contract " <> Text.pack (show inst) <> " has not requested endpoint " <> Text.pack endpointName)

    let handler _ = pure (UserEndpointResponse (EndpointDescription endpointName) (EndpointValue $ JSON.toJSON endpointValue))
    runRequestHandler (RequestHandler handler) inst activeEndpoints

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
    respondtoRequests @t @effs (contractRequestHandler @t @effs)
    logInfo "processAllContractOutboxes end"

contractRequestHandler ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member ChainIndexEffect effs
    , Member WalletEffect effs
    , Member SigningProcessEffect effs
    , Member Log effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
contractRequestHandler =
    processOwnPubkeyRequests @effs
    <> processAwaitSlotRequests @effs
    <> processUtxoAtRequests @effs
    <> processWriteTxRequests @t @effs
    <> processTxConfirmedRequests @effs
    <> processNextTxAtRequests @effs
