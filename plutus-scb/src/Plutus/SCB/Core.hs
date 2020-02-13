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
    ( simulate
    , dbStats
    , dbConnect
    , installContract
    , activateContract
    , reportContractStatus
    , installedContracts
    , installedContractsProjection
    , activeContracts
    , activeContractsProjection
    , activeContractHistory
    , Connection(Connection)
    , ContractCommand(..)
    , MonadContract
    , invokeContract
    , MonadEventStore
    , refreshProjection
    , runAggregateCommand
    , runGlobalQuery
    , updateContract
    , addProcessBus
    ) where

import           Control.Concurrent              (forkIO, myThreadId, threadDelay)
import           Control.Concurrent.Async        (concurrently_)
import           Control.Concurrent.STM          (TVar, atomically, newTVarIO, readTVarIO, writeTVar)
import           Control.Error.Util              (note)
import           Control.Monad                   (void, when)
import           Control.Monad.Except            (ExceptT, MonadError, throwError)
import           Control.Monad.Except.Extras     (mapError)
import           Control.Monad.IO.Class          (MonadIO, liftIO)
import           Control.Monad.IO.Unlift         (MonadUnliftIO)
import           Control.Monad.Logger            (LoggingT, MonadLogger, logDebugN, logInfoN, runStdoutLoggingT)
import           Control.Monad.Reader            (MonadReader, ReaderT, ask, runReaderT)
import           Control.Monad.Trans.Class       (lift)
import           Data.Aeson                      (FromJSON, ToJSON, withObject, (.:))
import qualified Data.Aeson                      as JSON
import           Data.Aeson.Types                (Parser)
import qualified Data.Aeson.Types                as JSON
import           Data.Foldable                   (traverse_)
import           Data.Map.Strict                 (Map)
import qualified Data.Map.Strict                 as Map
import           Data.Set                        (Set)
import qualified Data.Set                        as Set
import           Data.Text                       (Text)
import qualified Data.Text                       as Text
import qualified Data.UUID                       as UUID
import           Database.Persist.Sqlite         (ConnectionPool, createSqlitePoolFromInfo, mkSqliteConnectionInfo,
                                                  retryOnBusy, runSqlPool)
import           Eventful                        (Aggregate (Aggregate), EventStoreWriter, GlobalStreamProjection,
                                                  ProcessManager (ProcessManager), Projection,
                                                  StreamEvent (StreamEvent), UUID, VersionedEventStoreReader,
                                                  VersionedStreamEvent, aggregateCommandHandler, aggregateProjection,
                                                  applyProcessManagerCommandsAndEvents, commandStoredAggregate,
                                                  getLatestStreamProjection, globalStreamProjection, projectionMapMaybe,
                                                  serializedEventStoreWriter, serializedGlobalEventStoreReader,
                                                  serializedVersionedEventStoreReader, streamProjectionState,
                                                  synchronousEventBusWrapper, uuidNextRandom)
import           Eventful.Store.Sql              (JSONString, SqlEvent, SqlEventStoreConfig, defaultSqlEventStoreConfig,
                                                  jsonStringSerializer, sqlEventStoreReader, sqlGlobalEventStoreReader)
import           Eventful.Store.Sqlite           (sqliteEventStoreWriter)
import qualified Language.Plutus.Contract        as Contract
import qualified Language.Plutus.Contract.Wallet as Wallet
import qualified Ledger
import           Options.Applicative.Help.Pretty (pretty, (<+>))
import           Plutus.SCB.Arbitrary            (genResponse)
import           Plutus.SCB.Command              (saveRequestResponseAggregate, saveTxAggregate)
import           Plutus.SCB.Events               (ChainEvent (UserEvent), EventId (EventId),
                                                  RequestEvent (CancelRequest, IssueRequest),
                                                  ResponseEvent (ResponseEvent), Tx,
                                                  UserEvent (ContractStateTransition, InstallContract))
import qualified Plutus.SCB.Events               as Events
import           Plutus.SCB.Query                (balances, eventCount, latestContractStatus, monoidProjection,
                                                  nullProjection, requestStats, setProjection, trialBalance)
import qualified Plutus.SCB.Relation             as Relation
import           Plutus.SCB.Types                (ActiveContract (ActiveContract),
                                                  ActiveContractState (ActiveContractState), Contract (Contract),
                                                  DbConfig (DbConfig), PartiallyDecodedResponse,
                                                  SCBError (ActiveContractStateNotFound, ContractCommandError, ContractNotFound, WalletError),
                                                  activeContract, activeContractId, activeContractPath, contractPath,
                                                  dbConfigFile, dbConfigPoolSize, hooks, newState,
                                                  partiallyDecodedResponse)
import           Plutus.SCB.Utils                (liftError, logInfoS, render, tshow)
import           Test.QuickCheck                 (arbitrary, frequency, generate)
import           Wallet.API                      (NodeAPI, WalletAPI, WalletAPIError, WalletDiagnostics, logMsg)
import qualified Wallet.API                      as WAPI

data ThreadState
    = Running
    | Stopped
    deriving (Show, Eq)

newtype Connection =
    Connection (SqlEventStoreConfig SqlEvent JSONString, ConnectionPool)

-- | A long-ish running process that fills the database with lots of event data.
simulate :: (MonadIO m, MonadLogger m, MonadReader Connection m) => m ()
simulate = do
    logInfoN "Simulating"
    connection <- ask
    runWriters connection

-- | Dump various statistics and reports from various queries over the event store database.
dbStats :: (MonadLogger m, MonadEventStore ChainEvent m) => m ()
dbStats = do
    logInfoN "Querying"
    reportTrialBalance
    reportClosingBalances
    reportEventCount
    reportRequestStats

------------------------------------------------------------
-- | Write lots of events into the store. At the moment this code
-- exercises the eventstore and the multi-threaded generation/storage of
-- events.
runWriters ::
       forall m. (MonadLogger m, MonadIO m)
    => Connection
    -> m ()
runWriters connection = do
    threadState <- liftIO $ newTVarIO Running
        --
    logInfoN "Started writers"
    let writerAction =
            runStdoutLoggingT . flip runReaderT connection $ do
                tx :: Tx <- liftIO $ generate arbitrary
                void $ runAggregateCommand saveTxAggregate mockEventSource tx
                --
                requestId <- liftIO $ EventId <$> uuidNextRandom
                request <- liftIO $ generate arbitrary
                cancellation <-
                    liftIO $
                    generate $
                    frequency
                        [ (1, pure $ Just (CancelRequest requestId))
                        , (10, pure Nothing)
                        ]
                response <-
                    liftIO $
                    generate $
                    frequency
                        [ ( 10
                          , case genResponse request of
                                Nothing -> pure Nothing
                                Just generator ->
                                    Just . ResponseEvent requestId <$> generator)
                        , (1, pure Nothing)
                        ]
                me <- liftIO myThreadId
                logInfoN $ "(" <> tshow me <> ") Write"
                void $
                    runAggregateCommand
                        saveRequestResponseAggregate
                        contractEventSource
                        (IssueRequest requestId request, cancellation, response)
                liftIO pauseBeforeRepeat
        runWriterAction =
            void . forkIO $ repeatIOAction threadState writerAction
    liftIO $
        concurrently_
            (concurrently_ runWriterAction runWriterAction)
            (do pauseForWrites
                atomically $ writeTVar threadState Stopped)
    logInfoN "Stopped writers"
  where
    pauseForWrites = void $ threadDelay (5 * 60 * 1000 * 1000)
    pauseBeforeRepeat = void $ threadDelay (500 * 1000)

repeatIOAction :: TVar ThreadState -> IO a -> IO ()
repeatIOAction threadState action = go
  where
    go = do
        state <- readTVarIO threadState
        when (state == Running) $ do
            void action
            go

------------------------------------------------------------
reportTrialBalance :: (MonadLogger m, MonadEventStore ChainEvent m) => m ()
reportTrialBalance = do
    trialBalanceProjection <- runGlobalQuery trialBalance
    logInfoN "Trial Balance"
    logInfoS trialBalanceProjection

reportEventCount :: (MonadLogger m, MonadEventStore ChainEvent m) => m ()
reportEventCount = do
    eventCountProjection <- runGlobalQuery eventCount
    logInfoN $ "EventCount: " <> tshow eventCountProjection

reportRequestStats :: (MonadLogger m, MonadEventStore ChainEvent m) => m ()
reportRequestStats = do
    requestStatsProjection <- runGlobalQuery requestStats
    logInfoN $ render requestStatsProjection

reportClosingBalances :: (MonadLogger m, MonadEventStore ChainEvent m) => m ()
reportClosingBalances = do
    updatedProjection <- runGlobalQuery balances
    logInfoN "Closing Balances"
    let closingBalances = Relation.fromMap updatedProjection
    let report = (,) <$> Events.users <*> closingBalances
    logInfoS report

------------------------------------------------------------
installContract ::
       (MonadLogger m, MonadEventStore ChainEvent m) => FilePath -> m ()
installContract filePath = do
    logInfoN $ "Installing: " <> tshow filePath
    void $
        runAggregateCommand
            installCommand
            userEventSource
            (Contract {contractPath = filePath})
    logInfoN "Installed."

installCommand :: Aggregate () ChainEvent Contract
installCommand =
    Aggregate
        { aggregateProjection = nullProjection
        , aggregateCommandHandler =
              \() contract -> [UserEvent $ InstallContract contract]
        }

activateContract ::
       ( MonadIO m
       , MonadLogger m
       , MonadEventStore ChainEvent m
       , MonadContract m
       , MonadError SCBError m
       )
    => FilePath
    -> m ()
activateContract filePath = do
    logInfoN "Finding Contract"
    contract <- liftError $ lookupContract filePath
    activeContractId <- liftIO uuidNextRandom
    logInfoN "Initializing Contract"
    response <- liftError $ invokeContract $ InitContract (contractPath contract)
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
    void $
        runAggregateCommand
            saveContractState
            contractEventSource
            activeContractState
    logInfoN . render $
        "Installed:" <+> pretty (activeContract activeContractState)
    logInfoN "Done"

updateContract ::
       ( MonadLogger m
       , MonadEventStore ChainEvent m
       , MonadContract m
       , MonadError SCBError m
       , WalletAPI m
       , NodeAPI m
       , WalletDiagnostics m
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
        updateContract_ oldContractState endpointName endpointPayload
    case JSON.parseEither parseUnbalancedTxKey (hooks response) of
        Left err -> throwError $ ContractCommandError 0 $ Text.pack err
        Right unbalancedTxs -> do
            logInfoN $ "Balancing unbalanced TXs" <> tshow unbalancedTxs
            balancedTxs :: [Ledger.Tx] <-
                traverse
                    (mapError WalletError . Wallet.balanceWallet)
                    unbalancedTxs
            traverse_
                (runAggregateCommand saveBalancedTx walletEventSource)
                balancedTxs
                      --
            logInfoN $ "Submitting balanced TXs" <> tshow unbalancedTxs
            balanceResults :: [Ledger.TxId] <-
                traverse submitTxn balancedTxs
                      --
            traverse_
                (runAggregateCommand
                     saveBalancedTxResult
                     nodeEventSource)
                balanceResults
                      --
            let updatedContractState =
                    oldContractState
                        {partiallyDecodedResponse = response}
            logInfoN "Storing Updated Contract State"
            void $
                runAggregateCommand
                    saveContractState
                    contractEventSource
                    updatedContractState
            logInfoN . render $
                "Updated:" <+> pretty updatedContractState
            logInfoN "Done"

-- | A wrapper around the NodeAPI function that returns some more
-- useful evidence of the work done.
submitTxn :: (Monad m, NodeAPI m) => Ledger.Tx -> m Ledger.TxId
submitTxn txn = do
    WAPI.submitTxn txn
    pure $ Ledger.txId txn

parseUnbalancedTxKey :: JSON.Value -> Parser [Contract.UnbalancedTx]
parseUnbalancedTxKey = withObject "tx key" $ \o -> o .: "tx"

reportContractStatus ::
       (MonadLogger m, MonadEventStore ChainEvent m) => UUID -> m ()
reportContractStatus uuid = do
    logInfoN "Finding Contract"
    statuses <- runGlobalQuery latestContractStatus
    logInfoN $ render $ Map.lookup uuid statuses

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

class MonadContract m where
    invokeContract ::
           ContractCommand -> m (Either SCBError PartiallyDecodedResponse)

updateContract_ ::
       (MonadContract m, MonadError SCBError m)
    => ActiveContractState
    -> Text
    -> JSON.Value
    -> m PartiallyDecodedResponse
updateContract_ ActiveContractState { activeContract = ActiveContract {activeContractPath}
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

saveBalancedTx :: Aggregate () ChainEvent Ledger.Tx
saveBalancedTx = Aggregate {aggregateProjection, aggregateCommandHandler}
  where
    aggregateProjection = nullProjection
    aggregateCommandHandler _ txn = [Events.WalletEvent $ Events.BalancedTx txn]

saveBalancedTxResult :: Aggregate () ChainEvent Ledger.TxId
saveBalancedTxResult = Aggregate {aggregateProjection, aggregateCommandHandler}
  where
    aggregateProjection = nullProjection
    aggregateCommandHandler _ txId =
        [Events.NodeEvent $ Events.SubmittedTx txId]

saveContractState :: Aggregate () ChainEvent ActiveContractState
saveContractState =
    Aggregate {aggregateProjection = nullProjection, aggregateCommandHandler}
  where
    aggregateCommandHandler _ state =
        [UserEvent $ ContractStateTransition state]

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
-- TODO Perhaps we should change runAggregateCommand to take a closed list of sources, rather than any freeform UUID.
class Monad m =>
      MonadEventStore event m
    -- | Update a 'Projection'.
    where
    refreshProjection ::
           GlobalStreamProjection state event
        -> m (GlobalStreamProjection state event)
    -- | Update a command through an 'Aggregate'.
    runAggregateCommand ::
           Aggregate state event command -> UUID -> command -> m [event]

instance (FromJSON event, ToJSON event) =>
         MonadEventStore event (ReaderT Connection (LoggingT IO)) where
    refreshProjection projection = do
        (Connection (sqlConfig, connectionPool)) <- ask
        let reader =
                serializedGlobalEventStoreReader jsonStringSerializer $
                sqlGlobalEventStoreReader sqlConfig
        flip runSqlPool connectionPool $
            getLatestStreamProjection reader projection
    runAggregateCommand aggregate identifier input = do
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
            commandStoredAggregate writer reader aggregate identifier input

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
mockEventSource :: UUID
mockEventSource = UUID.fromWords 0 0 0 1

contractEventSource :: UUID
contractEventSource = UUID.fromWords 0 0 0 2

walletEventSource :: UUID
walletEventSource = UUID.fromWords 0 0 0 2

userEventSource :: UUID
userEventSource = UUID.fromWords 0 0 0 3

nodeEventSource :: UUID
nodeEventSource = UUID.fromWords 0 0 0 4

instance (WalletDiagnostics m, Monad m) =>
         WalletDiagnostics (ExceptT WalletAPIError m) where
    logMsg = lift . WAPI.logMsg

instance (WalletAPI m, Monad m) => WalletAPI (ExceptT WalletAPIError m) where
    ownPubKey = lift WAPI.ownPubKey
    sign = lift . WAPI.sign
    updatePaymentWithChange value inputs =
        lift $ WAPI.updatePaymentWithChange value inputs
    watchedAddresses = lift WAPI.watchedAddresses
    startWatching = lift . WAPI.startWatching
