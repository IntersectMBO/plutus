{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Plutus.SCB.Core
    ( dbConnect
    , installContract
    , activateContract
    , reportContractStatus
    , installedContracts
    , installedContractsProjection
    , activeContracts
    , txHistory
    , txHistoryProjection
    , activeContractsProjection
    , activeContractHistory
    , Connection(Connection)
    , ContractCommand(..)
    , MonadContract
    , invokeContract
    , MonadEventStore
    , refreshProjection
    , runCommand
    , runGlobalQuery
    , updateContract
    , addProcessBus
    , Source(..)
    , toUUID
    ) where

import           Cardano.Node.API                           (NodeFollowerAPI, subscribe)
import qualified Cardano.Node.API                           as NodeClient
import           Cardano.Node.Types                         (FollowerID)
import           Control.Error.Util                         (note)
import           Control.Lens                               (assign, modifying, use, _1, _2)
import           Control.Monad                              (void)
import           Control.Monad.Except                       (MonadError, throwError)
import           Control.Monad.Except.Extras                (mapError)
import           Control.Monad.IO.Class                     (MonadIO, liftIO)
import           Control.Monad.IO.Unlift                    (MonadUnliftIO)
import           Control.Monad.Logger                       (LoggingT, MonadLogger, logDebugN, logInfoN)
import           Control.Monad.Reader                       (MonadReader, ReaderT, ask)
import           Control.Monad.State                        (MonadState, StateT, execStateT)
import           Control.Monad.Trans                        (lift)
import           Data.Aeson                                 (FromJSON, ToJSON, withObject, (.:))
import qualified Data.Aeson                                 as JSON
import           Data.Aeson.Types                           (Parser)
import qualified Data.Aeson.Types                           as JSON
import           Data.Foldable                              (traverse_)
import           Data.Map.Strict                            (Map)
import qualified Data.Map.Strict                            as Map
import           Data.Set                                   (Set)
import qualified Data.Set                                   as Set
import           Data.Text                                  (Text)
import qualified Data.Text                                  as Text
import           Data.Text.Prettyprint.Doc                  (pretty, (<+>))
import           Database.Persist.Sqlite                    (ConnectionPool, createSqlitePoolFromInfo,
                                                             mkSqliteConnectionInfo, retryOnBusy, runSqlPool)
import           Eventful                                   (Aggregate, EventStoreWriter, GlobalStreamProjection,
                                                             ProcessManager (ProcessManager), Projection,
                                                             StreamEvent (StreamEvent), UUID, VersionedEventStoreReader,
                                                             VersionedStreamEvent, applyProcessManagerCommandsAndEvents,
                                                             commandStoredAggregate, getLatestStreamProjection,
                                                             globalStreamProjection, projectionMapMaybe,
                                                             serializedEventStoreWriter,
                                                             serializedGlobalEventStoreReader,
                                                             serializedVersionedEventStoreReader, streamProjectionState,
                                                             synchronousEventBusWrapper, uuidNextRandom)
import           Eventful.Store.Sql                         (JSONString, SqlEvent, SqlEventStoreConfig,
                                                             defaultSqlEventStoreConfig, jsonStringSerializer,
                                                             sqlEventStoreReader, sqlGlobalEventStoreReader)
import           Eventful.Store.Sqlite                      (sqliteEventStoreWriter)
import           Language.Plutus.Contract.Effects.OwnPubKey (OwnPubKeyRequest (NotWaitingForPubKey, WaitingForPubKey))
import qualified Language.Plutus.Contract.Wallet            as Wallet
import qualified Ledger
import           Ledger.Constraints                         (UnbalancedTx)
import           Plutus.SCB.Command                         (installCommand, saveBalancedTx, saveBalancedTxResult,
                                                             saveBlock, saveContractState)
import           Plutus.SCB.Events                          (ChainEvent (NodeEvent, UserEvent), NodeEvent (SubmittedTx),
                                                             UserEvent (ContractStateTransition, InstallContract))
import           Plutus.SCB.Query                           (blockCount, latestContractStatus, monoidProjection,
                                                             nullProjection, setProjection, utxoAt, utxoIndexProjection)
import           Plutus.SCB.Types                           (ActiveContract (ActiveContract),
                                                             ActiveContractState (ActiveContractState),
                                                             Contract (Contract),
                                                             ContractHook (OwnPubKeyHook, TxHook, UtxoAtHook),
                                                             DbConfig (DbConfig),
                                                             PartiallyDecodedResponse (PartiallyDecodedResponse),
                                                             SCBError (ActiveContractStateNotFound, ContractCommandError, ContractNotFound, WalletError),
                                                             Source (..), activeContract, activeContractId,
                                                             activeContractPath, contractPath, dbConfigFile,
                                                             dbConfigPoolSize, hooks, newState,
                                                             partiallyDecodedResponse, toUUID)
import           Plutus.SCB.Utils                           (liftError, render, tshow)
import           Wallet.API                                 (ChainIndexAPI, NodeAPI, SigningProcessAPI, WalletAPI,
                                                             WalletDiagnostics)
import qualified Wallet.API                                 as WAPI

newtype Connection =
    Connection (SqlEventStoreConfig SqlEvent JSONString, ConnectionPool)

installContract ::
       (MonadLogger m, MonadEventStore ChainEvent m) => FilePath -> m ()
installContract filePath = do
    logInfoN $ "Installing: " <> tshow filePath
    void $
        runCommand
            installCommand
            UserEventSource
            (Contract {contractPath = filePath})
    logInfoN "Installed."

activateContract ::
       ( MonadIO m
       , MonadLogger m
       , MonadEventStore ChainEvent m
       , MonadContract m
       , MonadError SCBError m
       )
    => FilePath
    -> m UUID
activateContract filePath = do
    logInfoN "Finding Contract"
    contract <- liftError $ lookupContract filePath
    activeContractId <- liftIO uuidNextRandom
    logInfoN "Initializing Contract"
    response <-
        liftError $ invokeContract $ InitContract (contractPath contract)
    let activeContractState =
            ActiveContractState
                { activeContract =
                      ActiveContract
                          { activeContractId
                          , activeContractPath = contractPath contract
                          }
                , partiallyDecodedResponse = response
                }
    logInfoN "Storing Initial Contract State"
    void $ runCommand saveContractState ContractEventSource activeContractState
    logInfoN . render $
        "Activated:" <+> pretty (activeContract activeContractState)
    logInfoN "Done"
    pure activeContractId

updateContract ::
       ( MonadLogger m
       , MonadEventStore ChainEvent m
       , MonadContract m
       , MonadError SCBError m
       , WalletAPI m
       , NodeAPI m
       , WalletDiagnostics m
       , ChainIndexAPI m
       , NodeFollowerAPI m
       , SigningProcessAPI m
       )
    => UUID
    -> Text
    -> JSON.Value
    -> m ()
updateContract uuid endpointName endpointPayload = do
    logInfoN "Finding Contract"
    oldContractState <- liftError $ lookupActiveContractState uuid
    logInfoN $
        "Updating Contract: " <>
        Text.pack (activeContractPath (activeContract oldContractState)) <>
        "/" <> endpointName
    fID <- subscribe
    void $
        execStateT
            (invokeContractUpdate fID $
             EventPayload endpointName endpointPayload)
            (oldContractState, [])
    --
    logInfoN "Handling Resulting Blockchain Events"
    logInfoN "Done"

parseSingleHook ::
       MonadError SCBError m
    => (JSON.Value -> Parser a)
    -> PartiallyDecodedResponse
    -> m a
parseSingleHook parser response =
    case JSON.parseEither parser (hooks response) of
        Left err     -> throwError $ ContractCommandError 0 $ Text.pack err
        Right result -> pure result

handleContractHook ::
       ( MonadError SCBError m
       , MonadLogger m
       , MonadEventStore ChainEvent m
       , WalletAPI m
       , WalletDiagnostics m
       , NodeAPI m
       , MonadContract m
       , MonadState (ActiveContractState, [ContractHook]) m
       , ChainIndexAPI m
       , NodeFollowerAPI m
       , SigningProcessAPI m
       )
    => FollowerID
    -> ContractHook
    -> m ()
handleContractHook _ (TxHook unbalancedTxs)  = handleTxHook unbalancedTxs
handleContractHook i (UtxoAtHook addresses)  = handleUtxoAtHook i addresses
handleContractHook i (OwnPubKeyHook request) = handleOwnPubKeyHook i request

handleTxHook ::
       ( MonadError SCBError m
       , MonadLogger m
       , MonadEventStore ChainEvent m
       , WalletAPI m
       , WalletDiagnostics m
       , NodeAPI m
       , ChainIndexAPI m
       , SigningProcessAPI m
       )
    => UnbalancedTx
    -> m ()
handleTxHook unbalancedTx = do
    logInfoN "Handling 'tx' hook."
    logInfoN $ "Balancing unbalanced TX: " <> tshow unbalancedTx
    balancedTx <- (mapError WalletError . Wallet.balanceWallet) unbalancedTx
    signedTx <- WAPI.signWithOwnPublicKey balancedTx
    logInfoN $ "Storing signed TX: " <> tshow signedTx
    void $ runCommand saveBalancedTx WalletEventSource balancedTx
    logInfoN $ "Submitting signed TX: " <> tshow signedTx
    balanceResult <- submitTx signedTx
    void $ runCommand saveBalancedTxResult NodeEventSource balanceResult

handleUtxoAtHook ::
       ( MonadError SCBError m
       , MonadContract m
       , MonadState (ActiveContractState, [ContractHook]) m
       , MonadEventStore ChainEvent m
       , MonadLogger m
       , WalletAPI m
       , WalletDiagnostics m
       , NodeAPI m
       , ChainIndexAPI m
       , NodeFollowerAPI m
       , SigningProcessAPI m
       )
    => FollowerID
    -> Ledger.Address
    -> m ()
handleUtxoAtHook i address = do
    logDebugN $ "Fetching utxo-at: " <> tshow address
    utxoIndex <- runGlobalQuery utxoIndexProjection
    let utxoAtAddress = utxoAt utxoIndex address
    logDebugN $ "Fetched utxo-at: " <> tshow utxoAtAddress
    invokeContractUpdate i $ EventPayload "utxo-at" (JSON.toJSON utxoAtAddress)

handleOwnPubKeyHook ::
       ( MonadError SCBError m
       , MonadContract m
       , MonadState (ActiveContractState, [ContractHook]) m
       , MonadEventStore ChainEvent m
       , MonadLogger m
       , WalletAPI m
       , ChainIndexAPI m
       , WalletDiagnostics m
       , NodeAPI m
       , NodeFollowerAPI m
       , SigningProcessAPI m
       )
    => FollowerID
    -> OwnPubKeyRequest
    -> m ()
handleOwnPubKeyHook _ NotWaitingForPubKey = pure ()
handleOwnPubKeyHook i WaitingForPubKey = do
    logInfoN "Handling 'own-pubkey' hook."
    key :: WAPI.PubKey <- WAPI.ownPubKey
    invokeContractUpdate i $ EventPayload "own-pubkey" (JSON.toJSON key)

-- | A wrapper around the NodeAPI function that returns some more
-- useful evidence of the work done.
submitTx :: (Monad m, NodeAPI m) => Ledger.Tx -> m Ledger.Tx
submitTx tx = do
    WAPI.submitTxn tx
    pure tx

parseHooks ::
       MonadError SCBError m => PartiallyDecodedResponse -> m [ContractHook]
parseHooks = parseSingleHook hookParser

hookParser :: JSON.Value -> Parser [ContractHook]
hookParser =
    withObject "Contract Hooks" $ \o -> do
        txHooks <- fmap TxHook <$> o .: "tx"
        utxoAtHooks <- fmap UtxoAtHook <$> o .: "utxo-at"
        ownPubKeyHook <- OwnPubKeyHook <$> o .: "own-pubkey"
        pure $ txHooks <> utxoAtHooks <> [ownPubKeyHook]

reportContractStatus ::
       (MonadLogger m, MonadEventStore ChainEvent m) => UUID -> m ()
reportContractStatus uuid = do
    logInfoN "Finding Contract"
    statuses <- runGlobalQuery latestContractStatus
    logInfoN $ render $ pretty $ Map.lookup uuid statuses

lookupContract ::
       MonadEventStore ChainEvent m => FilePath -> m (Either SCBError Contract)
lookupContract filePath = do
    installed <- installedContracts
    let matchingContracts =
            Set.filter
                (\Contract {contractPath} -> contractPath == filePath)
                installed
    pure $ note (ContractNotFound filePath) $ Set.lookupMin matchingContracts

lookupActiveContractState ::
       MonadEventStore ChainEvent m
    => UUID
    -> m (Either SCBError ActiveContractState)
lookupActiveContractState uuid = do
    active <- activeContractStates
    pure $ note (ActiveContractStateNotFound uuid) $ Map.lookup uuid active

data ContractCommand
    = InitContract FilePath
    | UpdateContract FilePath JSON.Value
    deriving (Show, Eq)

invokeContractUpdate ::
       ( MonadError SCBError m
       , MonadContract m
       , MonadState (ActiveContractState, [ContractHook]) m
       , MonadEventStore ChainEvent m
       , MonadLogger m
       , WalletAPI m
       , ChainIndexAPI m
       , WalletDiagnostics m
       , NodeAPI m
       , NodeFollowerAPI m
       , SigningProcessAPI m
       )
    => FollowerID
    -> Payload
    -> m ()
invokeContractUpdate i payload = do
    oldContractState <- use _1
    -- Invoke the contract. Get the repsonse.
    response <- invokeContractUpdate_ oldContractState payload
    let newContractState =
            oldContractState {partiallyDecodedResponse = response}
    logDebugN . render $ "Updated: " <+> pretty newContractState
    -- Store the new state
    logInfoN "Storing Updated Contract State"
    void $ runCommand saveContractState ContractEventSource newContractState
    -- Append the new hooks.
    newHooks <- parseHooks response
    assign _1 newContractState
    pushHooks newHooks
    processAllHooks i

processAllHooks ::
       ( MonadError SCBError m
       , MonadState (ActiveContractState, [ContractHook]) m
       , MonadEventStore ChainEvent m
       , MonadLogger m
       , MonadContract m
       , WalletAPI m
       , ChainIndexAPI m
       , WalletDiagnostics m
       , NodeAPI m
       , NodeFollowerAPI m
       , SigningProcessAPI m
       )
    => FollowerID
    -> m ()
processAllHooks i =
    popHook i >>= \case
        Nothing -> pure ()
        Just hook -> do
            handleContractHook i hook
            sync i
            processAllHooks i

sync ::
       (MonadLogger m, MonadEventStore ChainEvent m, NodeFollowerAPI m)
    => FollowerID
    -> m ()
sync i = do
    blocks <- NodeClient.blocks i
    traverse_ (runCommand saveBlock NodeEventSource) blocks
    count <- runGlobalQuery blockCount
    logDebugN $ "Block count is now: " <> tshow count

-- | Old hooks go to the back of the queue.
pushHooks ::
       (MonadState (ActiveContractState, [ContractHook]) m)
    => [ContractHook]
    -> m ()
pushHooks newHooks = modifying _2 (\oldHooks -> oldHooks <> newHooks)

popHook ::
       ( MonadEventStore ChainEvent m
       , MonadState (ActiveContractState, [ContractHook]) m
       , MonadLogger m
       , NodeFollowerAPI m
       )
    => FollowerID
    -> m (Maybe ContractHook)
popHook i = do
    oldHooks <- use _2
    logDebugN $ "Current Hooks: " <> tshow oldHooks
    case oldHooks of
        [] -> do
            sync i
            pure Nothing
        (hook:newHooks) -> do
            assign _2 newHooks
            pure $ Just hook

data Payload
    = EventPayload Text JSON.Value
    | HookPayload Text JSON.Value

encodePayload :: Payload -> (Text, JSON.Value)
encodePayload (HookPayload endpointName endpointValue) =
    (endpointName, endpointValue)
encodePayload (EventPayload endpointName endpointValue) =
    ( "event"
    , JSON.object [("tag", JSON.String endpointName), ("value", endpointValue)])

invokeContractUpdate_ ::
       (MonadContract m, MonadError SCBError m)
    => ActiveContractState
    -> Payload
    -> m PartiallyDecodedResponse
invokeContractUpdate_ ActiveContractState { activeContract = ActiveContract {activeContractPath}
                                          , partiallyDecodedResponse = PartiallyDecodedResponse {newState}
                                          } payload =
    liftError $
    invokeContract $
    UpdateContract activeContractPath $
    JSON.object [("oldState", newState), encodePayload payload]

installedContracts :: MonadEventStore ChainEvent m => m (Set Contract)
installedContracts = runGlobalQuery installedContractsProjection

installedContractsProjection ::
       Projection (Set Contract) (StreamEvent key position ChainEvent)
installedContractsProjection = projectionMapMaybe contractPaths setProjection
  where
    contractPaths (StreamEvent _ _ (UserEvent (InstallContract contract))) =
        Just contract
    contractPaths _ = Nothing

activeContracts :: MonadEventStore ChainEvent m => m (Set ActiveContract)
activeContracts = runGlobalQuery activeContractsProjection

activeContractsProjection ::
       Projection (Set ActiveContract) (StreamEvent key position ChainEvent)
activeContractsProjection = projectionMapMaybe contractPaths setProjection
  where
    contractPaths (StreamEvent _ _ (UserEvent (ContractStateTransition state))) =
        Just $ activeContract state
    contractPaths _ = Nothing

txHistory :: MonadEventStore ChainEvent m => m [Ledger.Tx]
txHistory = runGlobalQuery txHistoryProjection

txHistoryProjection ::
       Projection [Ledger.Tx] (StreamEvent key position ChainEvent)
txHistoryProjection = projectionMapMaybe submittedTxs monoidProjection
  where
    submittedTxs (StreamEvent _ _ (NodeEvent (SubmittedTx tx))) = Just [tx]
    submittedTxs _                                              = Nothing

activeContractHistory ::
       MonadEventStore ChainEvent m => UUID -> m [ActiveContractState]
activeContractHistory uuid = runGlobalQuery activeContractHistoryProjection
  where
    activeContractHistoryProjection ::
           Projection [ActiveContractState] (StreamEvent key position ChainEvent)
    activeContractHistoryProjection =
        projectionMapMaybe contractPaths monoidProjection
      where
        contractPaths (StreamEvent _ _ (UserEvent (ContractStateTransition state))) =
            if activeContractId (activeContract state) == uuid
                then Just [state]
                else Nothing
        contractPaths _ = Nothing

activeContractStates ::
       MonadEventStore ChainEvent m => m (Map UUID ActiveContractState)
activeContractStates = runGlobalQuery activeContractStatesProjection
  where
    activeContractStatesProjection ::
           Projection (Map UUID ActiveContractState) (StreamEvent key position ChainEvent)
    activeContractStatesProjection =
        projectionMapMaybe contractStatePaths monoidProjection
      where
        contractStatePaths (StreamEvent _ _ (UserEvent (ContractStateTransition state))) =
            Just $ Map.singleton (activeContractId (activeContract state)) state
        contractStatePaths _ = Nothing

------------------------------------------------------------
-- | Create a database 'Connection' containing the connection pool
-- plus some configuration information.
dbConnect ::
       (MonadUnliftIO m, MonadLogger m, MonadReader DbConfig m) => m Connection
dbConnect = do
    DbConfig {dbConfigFile, dbConfigPoolSize} <- ask
    let connectionInfo = mkSqliteConnectionInfo dbConfigFile
    logDebugN "Connecting to DB"
    connectionPool <- createSqlitePoolFromInfo connectionInfo dbConfigPoolSize
    pure $ Connection (defaultSqlEventStoreConfig, connectionPool)

------------------------------------------------------------
class Monad m =>
      MonadContract m
    where
    invokeContract ::
           ContractCommand -> m (Either SCBError PartiallyDecodedResponse)

instance MonadContract m => MonadContract (StateT state m) where
    invokeContract = lift . invokeContract

class Monad m =>
      MonadEventStore event m
    where
    refreshProjection ::
           GlobalStreamProjection state event
        -> m (GlobalStreamProjection state event)
    runCommand ::
           Aggregate state event command -> Source -> command -> m [event]

instance MonadEventStore event m => MonadEventStore event (StateT state m) where
    refreshProjection = lift . refreshProjection
    runCommand aggregate source command =
        lift $ runCommand aggregate source command

instance (FromJSON event, ToJSON event) =>
         MonadEventStore event (ReaderT Connection (LoggingT IO)) where
    refreshProjection projection = do
        (Connection (sqlConfig, connectionPool)) <- ask
        let reader =
                serializedGlobalEventStoreReader jsonStringSerializer $
                sqlGlobalEventStoreReader sqlConfig
        flip runSqlPool connectionPool $
            getLatestStreamProjection reader projection
    runCommand aggregate source input = do
        (Connection (sqlConfig, connectionPool)) <- ask
        let reader =
                serializedVersionedEventStoreReader jsonStringSerializer $
                sqlEventStoreReader sqlConfig
        let writer =
                addProcessBus
                    (serializedEventStoreWriter jsonStringSerializer $
                     sqliteEventStoreWriter sqlConfig)
                    reader
        retryOnBusy . flip runSqlPool connectionPool $
            commandStoredAggregate writer reader aggregate (toUUID source) input

runGlobalQuery ::
       MonadEventStore event m
    => Projection a (VersionedStreamEvent event)
    -> m a
runGlobalQuery query =
    fmap streamProjectionState <$> refreshProjection $
    globalStreamProjection query

addProcessBus ::
       Monad m
    => EventStoreWriter m event
    -> VersionedEventStoreReader m event
    -> EventStoreWriter m event
addProcessBus writer reader =
    synchronousEventBusWrapper
        writer
        [ \subwriter _ _ ->
              applyProcessManagerCommandsAndEvents
                  (ProcessManager nullProjection (const []) (const []))
                  subwriter
                  reader
                  ()
        ]
