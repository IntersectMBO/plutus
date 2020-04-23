{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
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
    , invokeContract
    , refreshProjection
    , runCommand
    , runGlobalQuery
    , updateContract
    , addProcessBus
    , Source(..)
    , toUUID
    -- * Effects
    , ContractEffects
    , SCBEffects
    ) where

import           Cardano.Node.RandomTx                      (GenRandomTx)
import           Cardano.Node.Types                         (FollowerID)
import           Control.Lens                               (_1, _2)
import           Control.Monad                              (void)
import           Control.Monad.Freer                        (Eff, Member, Members)
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.Extra.Log
import           Control.Monad.Freer.Extra.State            (assign, modifying, use)
import           Control.Monad.Freer.State                  (State, execState)
import           Control.Monad.IO.Unlift                    (MonadUnliftIO)
import           Control.Monad.Logger                       (MonadLogger)
import qualified Control.Monad.Logger                       as MonadLogger
import           Data.Aeson                                 (withObject, (.:))
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
import           Data.Text.Prettyprint.Doc                  (Pretty, pretty, (<+>))
import           Database.Persist.Sqlite                    (createSqlitePoolFromInfo, mkSqliteConnectionInfo)
import           Eventful                                   (Projection, StreamEvent (StreamEvent), UUID,
                                                             projectionMapMaybe)
import           Eventful.Store.Sql                         (defaultSqlEventStoreConfig)
import           Language.Plutus.Contract.Effects.OwnPubKey (OwnPubKeyRequest (NotWaitingForPubKey, WaitingForPubKey))
import qualified Language.Plutus.Contract.Wallet            as Wallet
import qualified Ledger
import qualified Ledger.AddressMap                          as AM
import           Ledger.Constraints.OffChain                (UnbalancedTx (unBalancedTxTx))
import           Plutus.SCB.Command                         (installCommand, saveBalancedTx, saveBalancedTxResult,
                                                             saveBlock, saveContractState)
import           Plutus.SCB.Events                          (ChainEvent (NodeEvent, UserEvent), NodeEvent (SubmittedTx),
                                                             UserEvent (ContractStateTransition, InstallContract))
import           Plutus.SCB.Query                           (blockCount, latestContractStatus, monoidProjection,
                                                             setProjection, utxoAt, utxoIndexProjection)
import           Plutus.SCB.Types                           (ActiveContract (ActiveContract),
                                                             ActiveContractState (ActiveContractState), ContractExe,
                                                             ContractHook (OwnPubKeyHook, TxHook, UtxoAtHook),
                                                             DbConfig (DbConfig),
                                                             PartiallyDecodedResponse (PartiallyDecodedResponse),
                                                             SCBError (ActiveContractStateNotFound, ContractCommandError, ContractNotFound),
                                                             Source (..), activeContract, activeContractDefinition,
                                                             activeContractInstanceId, dbConfigFile, dbConfigPoolSize,
                                                             hooks, newState, partiallyDecodedResponse, toUUID)
import           Plutus.SCB.Utils                           (render, tshow)
import qualified Wallet.API                                 as WAPI
import           Wallet.Emulator.MultiAgent                 (EmulatedWalletEffects)

import           Cardano.Node.Follower                      (NodeFollowerEffect, getBlocks, newFollower)
import           Plutus.SCB.Effects.Contract                (ContractCommand (..), ContractEffect, invokeContract)
import           Plutus.SCB.Effects.EventLog                (Connection (..), EventLogEffect, addProcessBus,
                                                             refreshProjection, runCommand, runGlobalQuery)
import qualified Plutus.SCB.Effects.EventLog                as EventLog
import           Plutus.SCB.Effects.UUID                    (UUIDEffect, uuidNextRandom)
import           Wallet.API                                 (WalletEffect)
import           Wallet.Effects                             (ChainIndexEffect, NodeClientEffect, SigningProcessEffect)
import qualified Wallet.Effects                             as WalletEffects

type ContractEffects t =
        '[ EventLogEffect (ChainEvent t)
         , Log
         , UUIDEffect
         , ContractEffect FilePath
         , Error SCBError
         ]

installContract ::
    forall t effs.
    ( Member Log effs
    , Member (EventLogEffect (ChainEvent t)) effs
    , Show t
    )
    => t
    -> Eff effs ()
installContract contractHandle = do
    logInfo $ "Installing: " <> tshow contractHandle
    void $
        runCommand
            installCommand
            UserEventSource
            contractHandle
    logInfo "Installed."

lookupContract ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member (Error SCBError) effs
    , Show t
    , Ord t
    )
    => t
    -> Eff effs t
lookupContract t = do
    installed <- installedContracts
    let matchingContracts =
            Set.filter
                (\cp -> cp == t)
                installed
    case Set.lookupMin matchingContracts of
        Just c  -> pure c
        Nothing -> throwError (ContractNotFound (show t))

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
    -> Eff effs UUID
activateContract filePath = do
    logInfo "Finding Contract"
    contract <- lookupContract @t filePath
    activeContractInstanceId <- uuidNextRandom
    logInfo "Initializing Contract"
    response <- invokeContract @t $ InitContract contract
    let activeContractState =
            ActiveContractState
                { activeContract =
                      ActiveContract
                          { activeContractInstanceId
                          , activeContractDefinition = contract
                          }
                , partiallyDecodedResponse = response
                }
    logInfo "Storing Initial Contract State"
    void $ runCommand saveContractState ContractEventSource activeContractState
    logInfo . render $
        "Activated:" <+> pretty (activeContract activeContractState)
    logInfo "Done"
    pure activeContractInstanceId

updateContract ::
    forall t effs.
       ( Members EmulatedWalletEffects effs
       , Member (Error SCBError) effs
       , Member (EventLogEffect (ChainEvent t)) effs
       , Member (ContractEffect t) effs
       , Member NodeFollowerEffect effs
       , Show t
       , Pretty t
       , Ord t
       )
    => UUID
    -> Text
    -> JSON.Value
    -> Eff effs ()
updateContract uuid endpointName endpointPayload = do
    logInfo "Finding Contract"
    oldContractState <- lookupActiveContractState @t uuid
    logInfo $
        "Updating Contract: " <>
        Text.pack (show $ activeContract oldContractState) <>
        "/" <> endpointName
    fID <- newFollower
    void
        $ execState @(ActiveContractStateHooks _)  (oldContractState, [])
        $ invokeContractUpdate @t fID (EventPayload endpointName endpointPayload)
    logInfo "Handling Resulting Blockchain Events"
    logInfo "Done"

parseSingleHook ::
    ( Member (Error SCBError) effs
    )
    => (JSON.Value -> Parser a)
    -> PartiallyDecodedResponse
    -> Eff effs a
parseSingleHook parser response =
    case JSON.parseEither parser (hooks response) of
        Left err     -> throwError $ ContractCommandError 0 $ Text.pack err
        Right result -> pure result

handleContractHook ::
    forall t effs.
       ( Members EmulatedWalletEffects effs
       , Member (Error SCBError) effs
       , Member (EventLogEffect (ChainEvent t)) effs
       , Member (State (ActiveContractStateHooks t)) effs
       , Member NodeFollowerEffect effs
       , Member (ContractEffect t) effs
       , Pretty t
       , Ord t
       )
    => FollowerID
    -> ContractHook
    -> Eff effs ()
handleContractHook _ (TxHook unbalancedTxs)  = handleTxHook @t unbalancedTxs
handleContractHook i (UtxoAtHook address)  =
    WalletEffects.startWatching address >> handleUtxoAtHook @t i address
handleContractHook i (OwnPubKeyHook request) = handleOwnPubKeyHook @t i request

handleTxHook ::
    forall t effs.
       ( Members EmulatedWalletEffects effs
       , Member (EventLogEffect (ChainEvent t)) effs
       )
    => UnbalancedTx
    -> Eff effs ()
handleTxHook unbalancedTx = do
    logInfo "Handling 'tx' hook."
    logInfo "Start watching contract addresses."
    AM.addressesTouched <$> WalletEffects.watchedAddresses <*> pure (unBalancedTxTx unbalancedTx) >>= traverse_ WalletEffects.startWatching
    logInfo $ "Balancing unbalanced TX: " <> tshow unbalancedTx
    balancedTx <- Wallet.balanceWallet unbalancedTx
    signedTx <- WAPI.signWithOwnPublicKey balancedTx
    logInfo $ "Storing signed TX: " <> tshow signedTx
    void $ runCommand (saveBalancedTx @t) WalletEventSource balancedTx
    logInfo $ "Submitting signed TX: " <> tshow signedTx
    balanceResult <- submitTx signedTx
    void $ runCommand (saveBalancedTxResult @t) NodeEventSource balanceResult

handleUtxoAtHook ::
    forall t effs.
       ( Member (Error SCBError) effs
       , Member (EventLogEffect (ChainEvent t)) effs
       , Member (State (ActiveContractStateHooks t)) effs
       , Member NodeFollowerEffect effs
       , Member (ContractEffect t) effs
       , Members EmulatedWalletEffects effs
       , Pretty t
       , Ord t
       )
    => FollowerID
    -> Ledger.Address
    -> Eff effs ()
handleUtxoAtHook i address = do
    logDebug $ "Fetching utxo-at: " <> tshow address
    utxoIndex <- runGlobalQuery (utxoIndexProjection @t)
    let utxoAtAddress = utxoAt utxoIndex address
    logDebug $ "Fetched utxo-at: " <> tshow utxoAtAddress
    invokeContractUpdate @t i $ EventPayload "utxo-at" (JSON.toJSON utxoAtAddress)

handleOwnPubKeyHook ::
    forall t effs.
       ( Member (Error SCBError) effs
       , Member (EventLogEffect (ChainEvent t)) effs
       , Member (State (ActiveContractStateHooks t)) effs
       , Member NodeFollowerEffect effs
       , Member (ContractEffect t) effs
       , Members EmulatedWalletEffects effs
       , Pretty t
       , Ord t
       )
    => FollowerID
    -> OwnPubKeyRequest
    -> Eff effs ()
handleOwnPubKeyHook _ NotWaitingForPubKey = pure ()
handleOwnPubKeyHook i WaitingForPubKey = do
    logInfo "Handling 'own-pubkey' hook."
    key :: WAPI.PubKey <- WAPI.ownPubKey
    invokeContractUpdate @t i $ EventPayload "own-pubkey" (JSON.toJSON key)

-- | A wrapper around the NodeAPI function that returns some more
-- useful evidence of the work done.
submitTx :: (Member WalletEffect effs) => Ledger.Tx -> Eff effs Ledger.Tx
submitTx tx = do
    WAPI.submitTxn tx
    pure tx

parseHooks ::
       Member (Error SCBError) effs => PartiallyDecodedResponse -> Eff effs [ContractHook]
parseHooks = parseSingleHook hookParser

hookParser :: JSON.Value -> Parser [ContractHook]
hookParser =
    withObject "Contract Hooks" $ \o -> do
        txHooks <- fmap TxHook <$> o .: "tx"
        utxoAtHooks <- fmap UtxoAtHook <$> o .: "utxo-at"
        ownPubKeyHook <- OwnPubKeyHook <$> o .: "own-pubkey"
        pure $ txHooks <> utxoAtHooks <> [ownPubKeyHook]

reportContractStatus ::
    forall t effs.
    ( Member Log effs
    , Member (EventLogEffect (ChainEvent t)) effs
    , Pretty t
    )
    => UUID
    -> Eff effs ()
reportContractStatus uuid = do
    logInfo "Finding Contract"
    statuses <- runGlobalQuery (latestContractStatus @t)
    logInfo $ render $ pretty $ Map.lookup uuid statuses

lookupActiveContractState ::
    forall t effs.
    ( Member (Error SCBError) effs
    , Member (EventLogEffect (ChainEvent t)) effs
    )
    => UUID
    -> Eff effs (ActiveContractState t)
lookupActiveContractState uuid = do
    active <- activeContractStates
    case Map.lookup uuid active of
        Nothing -> throwError (ActiveContractStateNotFound uuid)
        Just s  -> return s

type ActiveContractStateHooks t = (ActiveContractState t, [ContractHook])

invokeContractUpdate ::
       forall t effs.
       ( Member (EventLogEffect (ChainEvent t)) effs
       , Member (Error SCBError) effs
       , Member (State (ActiveContractStateHooks t )) effs
       , Member NodeFollowerEffect effs
       , Member (ContractEffect t) effs
       , Members EmulatedWalletEffects effs
       , Pretty t
       , Ord t
       )
    => FollowerID
    -> Payload
    -> Eff effs ()
invokeContractUpdate i payload = do
    oldContractState <- use @(ActiveContractStateHooks t) _1
    -- Invoke the contract. Get the repsonse.
    response <- invokeContractUpdate_ oldContractState payload
    let newContractState =
            oldContractState {partiallyDecodedResponse = response}
    logDebug . render $ "Updated: " <+> pretty newContractState
    -- Store the new state
    logInfo "Storing Updated Contract State"
    void $ runCommand saveContractState ContractEventSource newContractState
    -- Append the new hooks.
    newHooks <- parseHooks response
    assign @(ActiveContractStateHooks t) _1 newContractState
    pushHooks @t newHooks
    processAllHooks @t i

processAllHooks ::
    forall t effs.
       ( Members EmulatedWalletEffects effs
       , Member (Error SCBError) effs
       , Member (EventLogEffect (ChainEvent t)) effs
       , Member (State (ActiveContractStateHooks t)) effs
       , Member NodeFollowerEffect effs
       , Member (ContractEffect t) effs
       , Pretty t
       , Ord t
       )
    => FollowerID
    -> Eff effs ()
processAllHooks i =
    popHook @t i >>= \case
        Nothing -> pure ()
        Just hook -> do
            handleContractHook @t i hook
            sync @t i
            processAllHooks @t i

sync ::
    forall t effs.
       ( Member NodeFollowerEffect effs
       , Member (EventLogEffect (ChainEvent t)) effs
       , Member Log effs
       )
    => FollowerID
    -> Eff effs ()
sync i = do
    blocks <- getBlocks i
    traverse_ (runCommand (saveBlock @t) NodeEventSource) blocks
    count <- runGlobalQuery (blockCount @t)
    logDebug $ "Block count is now: " <> tshow count

-- | Old hooks go to the back of the queue.
pushHooks ::
    forall t effs.
       (Member (State (ActiveContractStateHooks t)) effs)
    => [ContractHook]
    -> Eff effs ()
pushHooks newHooks = modifying @(ActiveContractStateHooks t) _2 (\oldHooks -> oldHooks <> newHooks)

popHook ::
    forall t effs.
       ( Member (State (ActiveContractStateHooks t)) effs
       , Member Log effs
       , Member (EventLogEffect (ChainEvent t)) effs
       , Member NodeFollowerEffect effs
       )
    => FollowerID
    -> Eff effs (Maybe ContractHook)
popHook i = do
    oldHooks <- use @(ActiveContractStateHooks t) _2
    logDebug $ "Current Hooks: " <> tshow oldHooks
    case oldHooks of
        [] -> do
            sync @t i
            pure Nothing
        (hook:newHooks) -> do
            assign @(ActiveContractStateHooks t) _2 newHooks
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
       (Member (ContractEffect t) effs)
    => ActiveContractState t
    -> Payload
    -> Eff effs PartiallyDecodedResponse
invokeContractUpdate_ ActiveContractState { activeContract = ActiveContract {activeContractDefinition}
                                          , partiallyDecodedResponse = PartiallyDecodedResponse {newState}
                                          } payload =
    invokeContract $
    UpdateContract activeContractDefinition $
    JSON.object [("oldState", newState), encodePayload payload]

installedContracts :: forall t effs. (Ord t, Member (EventLogEffect (ChainEvent t)) effs) => Eff effs (Set t)
installedContracts = runGlobalQuery installedContractsProjection

installedContractsProjection ::
    forall t key position.
    Ord t => Projection (Set t) (StreamEvent key position (ChainEvent t))
installedContractsProjection = projectionMapMaybe contractPaths setProjection
  where
    contractPaths (StreamEvent _ _ (UserEvent (InstallContract contract))) =
        Just contract
    contractPaths _ = Nothing

activeContracts :: forall t effs. (Ord t, Member (EventLogEffect (ChainEvent t)) effs) => Eff effs (Set (ActiveContract t))
activeContracts = runGlobalQuery activeContractsProjection

activeContractsProjection ::
    forall t key position. Ord t =>
       Projection (Set (ActiveContract t)) (StreamEvent key position (ChainEvent t))
activeContractsProjection = projectionMapMaybe contractPaths setProjection
  where
    contractPaths (StreamEvent _ _ (UserEvent (ContractStateTransition state))) =
        Just $ activeContract state
    contractPaths _ = Nothing

txHistory :: forall t effs. (Member (EventLogEffect (ChainEvent t)) effs) => Eff effs [Ledger.Tx]
txHistory = runGlobalQuery (txHistoryProjection @t)

txHistoryProjection ::
    forall t key position.
       Projection [Ledger.Tx] (StreamEvent key position (ChainEvent t))
txHistoryProjection = projectionMapMaybe submittedTxs monoidProjection
  where
    submittedTxs (StreamEvent _ _ (NodeEvent (SubmittedTx tx))) = Just [tx]
    submittedTxs _                                              = Nothing

activeContractHistory ::
       Member (EventLogEffect (ChainEvent t)) effs => UUID -> Eff effs [ActiveContractState t]
activeContractHistory uuid = runGlobalQuery activeContractHistoryProjection
  where
    activeContractHistoryProjection ::
           Projection [ActiveContractState t] (StreamEvent key position (ChainEvent t))
    activeContractHistoryProjection =
        projectionMapMaybe contractPaths monoidProjection
      where
        contractPaths (StreamEvent _ _ (UserEvent (ContractStateTransition state))) =
            if activeContractInstanceId (activeContract state) == uuid
                then Just [state]
                else Nothing
        contractPaths _ = Nothing

activeContractStates ::
    forall t effs.
       Member (EventLogEffect (ChainEvent t)) effs => Eff effs (Map UUID (ActiveContractState t))
activeContractStates = runGlobalQuery activeContractStatesProjection
  where
    activeContractStatesProjection ::
           Projection (Map UUID (ActiveContractState t)) (StreamEvent key position (ChainEvent t))
    activeContractStatesProjection =
        projectionMapMaybe contractStatePaths monoidProjection
      where
        contractStatePaths (StreamEvent _ _ (UserEvent (ContractStateTransition state))) =
            Just $ Map.singleton (activeContractInstanceId (activeContract state)) state
        contractStatePaths _ = Nothing

------------------------------------------------------------
-- | Create a database 'Connection' containing the connection pool
-- plus some configuration information.
dbConnect ::
    ( MonadUnliftIO m
    , MonadLogger m
    )
    => DbConfig
    -> m EventLog.Connection
dbConnect DbConfig {dbConfigFile, dbConfigPoolSize} = do
    let connectionInfo = mkSqliteConnectionInfo dbConfigFile
    MonadLogger.logDebugN "Connecting to DB"
    connectionPool <- createSqlitePoolFromInfo connectionInfo dbConfigPoolSize
    pure $ EventLog.Connection (defaultSqlEventStoreConfig, connectionPool)

type SCBEffects =
        '[ GenRandomTx
        , NodeFollowerEffect
        , WalletEffect
        , UUIDEffect
        , ContractEffect ContractExe
        , ChainIndexEffect
        , NodeClientEffect
        , SigningProcessEffect
        , EventLogEffect (ChainEvent ContractExe)
        , Log
        ]
