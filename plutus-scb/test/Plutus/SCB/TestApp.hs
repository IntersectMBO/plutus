{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE TemplateHaskell            #-}

-- | A test version of the 'App' stack which runs all operations in memory.
-- No networking, no filesystem.
module Plutus.SCB.TestApp
    ( runScenario
    ) where

import qualified Cardano.Node.Mock                             as NodeClient
import qualified Cardano.Node.Types                            as NodeClient
import qualified Cardano.Wallet.Mock                           as WalletClient
import           Control.Concurrent.MVar                       (MVar, newMVar, putMVar, takeMVar)
import           Control.Lens                                  (makeLenses, set, view, zoom)
import           Control.Monad                                 (void)
import           Control.Monad.Except                          (ExceptT, MonadError, runExceptT)
import           Control.Monad.Freer                           (Eff, runM)
import qualified Control.Monad.Freer.State                     as FS
import           Control.Monad.IO.Class                        (MonadIO, liftIO)
import           Control.Monad.Logger                          (LoggingT, MonadLogger, logInfoN, runStderrLoggingT)
import           Control.Monad.State                           (MonadState, StateT (StateT), execStateT, runStateT)
import           Data.Aeson                                    as JSON
import           Data.Aeson.Types                              as JSON
import           Data.Bifunctor                                (first)
import           Data.Text                                     (Text)
import qualified Data.Text                                     as Text
import           Eventful                                      (commandStoredAggregate, getLatestStreamProjection)
import           Eventful.Store.Memory                         (EventMap, emptyEventMap, stateEventStoreReader,
                                                                stateEventStoreWriter, stateGlobalEventStoreReader)
import           Language.Plutus.Contract.Resumable            (ResumableError)
import           Language.Plutus.Contract.Servant              (initialResponse, runUpdate)
import qualified Language.PlutusTx.Coordination.Contracts.Game as Contracts.Game
import qualified Ledger
import qualified Ledger.AddressMap                             as AM
import           Plutus.SCB.Command                            ()
import           Plutus.SCB.Core
import           Plutus.SCB.Events                             (ChainEvent)
import           Plutus.SCB.Types                              (SCBError (ContractCommandError, ContractNotFound))
import           Test.QuickCheck.Instances.UUID                ()
import           Wallet.API                                    (ChainIndexAPI, NodeAPI, WalletAPI, WalletDiagnostics,
                                                                logMsg, ownOutputs, ownPubKey, sign, slot,
                                                                startWatching, submitTxn, updatePaymentWithChange,
                                                                watchedAddresses)

data TestState =
    TestState
        { _eventStore  :: EventMap ChainEvent
        , _walletState :: WalletClient.State
        , _nodeState   :: MVar NodeClient.AppState
        }

makeLenses 'TestState

newtype TestApp a =
    TestApp (StateT TestState (LoggingT (ExceptT SCBError IO)) a)
    deriving newtype ( Functor
                     , Applicative
                     , Monad
                     , MonadLogger
                     , MonadIO
                     , MonadState TestState
                     , MonadError SCBError
                     )

initialTestState :: MonadIO m => m TestState
initialTestState =
    liftIO $ do
        let _eventStore = emptyEventMap
        -- ^ Set up the event log.
        -- Set up the node.
        _nodeState <- liftIO $ newMVar NodeClient.initialAppState
        runStderrLoggingT $
            NodeClient.processChainEffects _nodeState NodeClient.addBlock
        let getBlockchain =
                liftIO $ do
                    oldState <- takeMVar _nodeState
                    (chain, newChainState) <-
                        runM $
                        FS.runState
                            (view NodeClient.chainState oldState)
                            NodeClient.blockchain
                    let newState =
                            set NodeClient.chainState newChainState oldState
                    putMVar _nodeState newState
                    pure $ Right chain
        -- Set up the wallet.
        _walletState <-
            execStateT
                (WalletClient.syncState getBlockchain)
                WalletClient.initialState
        pure TestState {_eventStore, _nodeState, _walletState}

runScenario :: TestApp a -> IO ()
runScenario (TestApp action) = do
    testState <- initialTestState
    result <- runExceptT $ runStderrLoggingT $ runStateT action testState
    case result of
        Left err -> error $ show err
        Right _  -> pure ()

instance MonadEventStore ChainEvent TestApp where
    refreshProjection projection =
        TestApp . zoom eventStore $
        getLatestStreamProjection stateGlobalEventStoreReader projection
    runCommand aggregate source command =
        TestApp . zoom eventStore $
        commandStoredAggregate
            stateEventStoreWriter
            stateEventStoreReader
            aggregate
            (toUUID source)
            command

instance MonadContract TestApp where
    invokeContract (InitContract "game") =
        pure $ do
            value <- fromResumable $ initialResponse Contracts.Game.game
            fromString $ JSON.eitherDecode (JSON.encode value)
    invokeContract (UpdateContract "game" payload) =
        pure $ do
            request <- fromString $ JSON.parseEither JSON.parseJSON payload
            value <- fromResumable $ runUpdate Contracts.Game.game request
            fromString $ JSON.eitherDecode (JSON.encode value)
    invokeContract (InitContract contractPath) =
        pure $ Left $ ContractNotFound contractPath
    invokeContract (UpdateContract contractPath _) =
        pure $ Left $ ContractNotFound contractPath

instance WalletDiagnostics TestApp where
    logMsg = logInfoN

instance WalletAPI TestApp where
    ownPubKey = WalletClient.getOwnPubKey
    sign = WalletClient.sign
    updatePaymentWithChange _ _ = error "UNIMPLEMENTED: updatePaymentWithChange"
    ownOutputs = do
        pk <- ownPubKey
        am <- watchedAddresses
        pure $ view (AM.fundsAt (Ledger.pubKeyAddress pk)) am

instance ChainIndexAPI TestApp where
    watchedAddresses =
        TestApp . zoom walletState $ WalletClient.getWatchedAddresses
    startWatching address =
        TestApp . zoom walletState $ void $ WalletClient.startWatching address

instance NodeAPI TestApp where
    submitTxn txn = runChainEffects $ void $ NodeClient.addTx txn
    slot = runChainEffects NodeClient.getCurrentSlot

runChainEffects :: Eff (NodeClient.NodeServerEffects IO) a -> TestApp a
runChainEffects action =
    TestApp . zoom nodeState . StateT $ \stateMVar -> do
        result <- NodeClient.processChainEffects stateMVar action
        pure (result, stateMVar)

fromString :: Either String a -> Either SCBError a
fromString = first (ContractCommandError 0 . Text.pack)

fromResumable :: Either (ResumableError Text) a -> Either SCBError a
fromResumable = first (ContractCommandError 0 . Text.pack . show)
