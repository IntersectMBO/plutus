{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
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

import           Control.Error.Util                         (note)
import           Control.Monad                              (void)
import           Control.Monad.Except                       (MonadError, throwError)
import           Control.Monad.Except.Extras                (mapError)
import           Control.Monad.IO.Class                     (MonadIO, liftIO)
import           Control.Monad.IO.Unlift                    (MonadUnliftIO)
import           Control.Monad.Logger                       (LoggingT, MonadLogger, logDebugN, logInfoN, logWarnN)
import           Control.Monad.Reader                       (MonadReader, ReaderT, ask)
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
import qualified Data.UUID                                  as UUID
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
import           Language.Plutus.Contract.Effects.OwnPubKey (OwnPubKeyRequest)
import qualified Language.Plutus.Contract.Wallet            as Wallet
import qualified Ledger
import qualified Ledger.Constraints                         as Ledger
import           Plutus.SCB.Command                         (installCommand, saveBalancedTx, saveBalancedTxResult,
                                                             saveContractState)
import           Plutus.SCB.Events                          (ChainEvent (NodeEvent, UserEvent), NodeEvent (SubmittedTx),
                                                             UserEvent (ContractStateTransition, InstallContract))
import           Plutus.SCB.Query                           (latestContractStatus, monoidProjection, nullProjection,
                                                             setProjection)
import           Plutus.SCB.Types                           (ActiveContract (ActiveContract),
                                                             ActiveContractState (ActiveContractState),
                                                             Contract (Contract), DbConfig (DbConfig),
                                                             PartiallyDecodedResponse,
                                                             SCBError (ActiveContractStateNotFound, ContractCommandError, ContractNotFound, WalletError),
                                                             activeContract, activeContractId, activeContractPath,
                                                             contractPath, dbConfigFile, dbConfigPoolSize, hooks,
                                                             newState, partiallyDecodedResponse)
import           Plutus.SCB.Utils                           (liftError, render, tshow)
import           Wallet.API                                 (ChainIndexAPI, NodeAPI, WalletAPI, WalletDiagnostics)
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
       )
    => UUID
    -> Text
    -> JSON.Value
    -> m ()
updateContract uuid endpointName endpointPayload = do
    logInfoN "Finding Contract"
    oldContractState <- liftError $ lookupActiveContractState uuid
    logInfoN "Updating Contract"
    response <-
        invokeContractUpdate oldContractState endpointName endpointPayload
    let newContractState =
            oldContractState {partiallyDecodedResponse = response}
    logInfoN . render $ "Updated:" <+> pretty newContractState
    logInfoN "Storing Updated Contract State"
    void $ runCommand saveContractState ContractEventSource newContractState
    --
    logInfoN "Handling Resulting Blockchain Events"
    handleBlockchainEvents response
    logInfoN "Done"

handleBlockchainEvents ::
       ( MonadError SCBError m
       , MonadLogger m
       , MonadEventStore ChainEvent m
       , WalletAPI m
       , WalletDiagnostics m
       , NodeAPI m
       , ChainIndexAPI m
       )
    => PartiallyDecodedResponse
    -> m ()
handleBlockchainEvents response = do
    handleTxHook response
    handleUtxoAtHook response
    handleOwnPubKeyHook response

parseSingleHook ::
       MonadError SCBError m
    => (JSON.Value -> Parser a)
    -> PartiallyDecodedResponse
    -> m a
parseSingleHook parser response =
    case JSON.parseEither parser (hooks response) of
        Left err     -> throwError $ ContractCommandError 0 $ Text.pack err
        Right result -> pure result

handleTxHook ::
       ( MonadError SCBError m
       , MonadLogger m
       , MonadEventStore ChainEvent m
       , WalletAPI m
       , WalletDiagnostics m
       , NodeAPI m
       , ChainIndexAPI m
       )
    => PartiallyDecodedResponse
    -> m ()
handleTxHook response = do
    logInfoN "Handling 'tx' hook."
    unbalancedTxs <- parseSingleHook txKeyParser response
    logInfoN $ "Balancing unbalanced TXs: " <> tshow unbalancedTxs
    balancedTxs <-
        traverse (mapError WalletError . Wallet.balanceWallet) unbalancedTxs
    traverse_ (runCommand saveBalancedTx WalletEventSource) balancedTxs
    --
    logInfoN $ "Submitting balanced TXs: " <> tshow unbalancedTxs
    balanceResults <- traverse submitTxn balancedTxs
    traverse_ (runCommand saveBalancedTxResult NodeEventSource) balanceResults

handleUtxoAtHook ::
       (MonadError SCBError m, MonadLogger m)
    => PartiallyDecodedResponse
    -> m ()
handleUtxoAtHook response = do
    logInfoN "Handling 'utxo-at' hook."
    utxoAts <- parseSingleHook utxoAtKeyParser response
    traverse_ (logInfoN . tshow) utxoAts
    logWarnN "UNIMPLEMENTED: handleUtxoAtHook"

handleOwnPubKeyHook ::
       (MonadError SCBError m, MonadLogger m)
    => PartiallyDecodedResponse
    -> m ()
handleOwnPubKeyHook response = do
    logInfoN "Handling 'own-pubkey' hook."
    ownPubKeys <- parseSingleHook ownPubKeyParser response
    logInfoN $ tshow ownPubKeys
    logWarnN "UNIMPLEMENTED: handleOwnPubKeyHook"

-- | A wrapper around the NodeAPI function that returns some more
-- useful evidence of the work done.
submitTxn :: (Monad m, NodeAPI m) => Ledger.Tx -> m Ledger.Tx
submitTxn txn = do
    WAPI.submitTxn txn
    pure txn

txKeyParser :: JSON.Value -> Parser [Ledger.UnbalancedTx]
txKeyParser = withObject "tx key" $ \o -> o .: "tx"

utxoAtKeyParser :: JSON.Value -> Parser [Ledger.Address]
utxoAtKeyParser = withObject "utxo-at key" $ \o -> o .: "utxo-at"

ownPubKeyParser :: JSON.Value -> Parser OwnPubKeyRequest
ownPubKeyParser = withObject "own-pubkey key" $ \o -> o .: "own-pubkey"

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
       (MonadContract m, MonadError SCBError m)
    => ActiveContractState
    -> Text
    -> JSON.Value
    -> m PartiallyDecodedResponse
invokeContractUpdate ActiveContractState { activeContract = ActiveContract {activeContractPath}
                                         , partiallyDecodedResponse
                                         } endpointName endpointPayload =
    liftError $
    invokeContract $
    UpdateContract activeContractPath $
    JSON.object
        [ ("oldState", newState partiallyDecodedResponse)
        , ( "event"
          , JSON.object
                [("tag", JSON.String endpointName), ("value", endpointPayload)])
        ]

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
class MonadContract m where
    invokeContract ::
           ContractCommand -> m (Either SCBError PartiallyDecodedResponse)

class Monad m =>
      MonadEventStore event m
    where
    refreshProjection ::
           GlobalStreamProjection state event
        -> m (GlobalStreamProjection state event)
    runCommand ::
           Aggregate state event command -> Source -> command -> m [event]

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

------------------------------------------------------------
data Source
    = ContractEventSource
    | WalletEventSource
    | UserEventSource
    | NodeEventSource
    deriving (Show, Eq)

toUUID :: Source -> UUID
toUUID ContractEventSource = UUID.fromWords 0 0 0 1
toUUID WalletEventSource   = UUID.fromWords 0 0 0 2
toUUID UserEventSource     = UUID.fromWords 0 0 0 3
toUUID NodeEventSource     = UUID.fromWords 0 0 0 4
