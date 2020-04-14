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
import           Data.Text.Prettyprint.Doc                  (pretty, (<+>))
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
                                                             ActiveContractState (ActiveContractState),
                                                             Contract (Contract),
                                                             ContractHook (OwnPubKeyHook, TxHook, UtxoAtHook),
                                                             DbConfig (DbConfig),
                                                             PartiallyDecodedResponse (PartiallyDecodedResponse),
                                                             SCBError (ActiveContractStateNotFound, ContractCommandError, ContractNotFound),
                                                             Source (..), activeContract, activeContractId,
                                                             activeContractPath, contractPath, dbConfigFile,
                                                             dbConfigPoolSize, hooks, newState,
                                                             partiallyDecodedResponse, toUUID)
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

type ContractEffects =
        '[ EventLogEffect ChainEvent
         , Log
         , UUIDEffect
         , ContractEffect
         , Error SCBError
         ]

installContract ::
    ( Member Log effs
    , Member (EventLogEffect ChainEvent) effs
    )
    => FilePath
    -> Eff effs ()
installContract filePath = do
    logInfo $ "Installing: " <> tshow filePath
    void $
        runCommand
            installCommand
            UserEventSource
            (Contract {contractPath = filePath})
    logInfo "Installed."

lookupContract ::
    ( Member (EventLogEffect ChainEvent) effs
    , Member (Error SCBError) effs
    )
    => FilePath
    -> Eff effs Contract
lookupContract filePath = do
    installed <- installedContracts
    let matchingContracts =
            Set.filter
                (\Contract {contractPath} -> contractPath == filePath)
                installed
    case Set.lookupMin matchingContracts of
        Just c  -> pure c
        Nothing -> throwError (ContractNotFound filePath)

activateContract ::
    ( Member Log effs
    , Member (EventLogEffect ChainEvent) effs
    , Member (Error SCBError) effs
    , Member UUIDEffect effs
    , Member ContractEffect effs
    )
    => FilePath
    -> Eff effs UUID
activateContract filePath = do
    logInfo "Finding Contract"
    contract <- lookupContract filePath
    activeContractId <- uuidNextRandom
    logInfo "Initializing Contract"
    response <- invokeContract $ InitContract (contractPath contract)
    let activeContractState =
            ActiveContractState
                { activeContract =
                      ActiveContract
                          { activeContractId
                          , activeContractPath = contractPath contract
                          }
                , partiallyDecodedResponse = response
                }
    logInfo "Storing Initial Contract State"
    void $ runCommand saveContractState ContractEventSource activeContractState
    logInfo . render $
        "Activated:" <+> pretty (activeContract activeContractState)
    logInfo "Done"
    pure activeContractId

updateContract ::
       ( Members EmulatedWalletEffects effs
       , Member (Error SCBError) effs
       , Member (EventLogEffect ChainEvent) effs
       , Member ContractEffect effs
       , Member NodeFollowerEffect effs
       )
    => UUID
    -> Text
    -> JSON.Value
    -> Eff effs ()
updateContract uuid endpointName endpointPayload = do
    logInfo "Finding Contract"
    oldContractState <- lookupActiveContractState uuid
    logInfo $
        "Updating Contract: " <>
        Text.pack (activeContractPath (activeContract oldContractState)) <>
        "/" <> endpointName
    fID <- newFollower
    void
        $ execState @T  (oldContractState, [])
        $ invokeContractUpdate fID (EventPayload endpointName endpointPayload)
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
       ( Members EmulatedWalletEffects effs
       , Member (Error SCBError) effs
       , Member (EventLogEffect ChainEvent) effs
       , Member (State T) effs
       , Member NodeFollowerEffect effs
       , Member ContractEffect effs
       )
    => FollowerID
    -> ContractHook
    -> Eff effs ()
handleContractHook _ (TxHook unbalancedTxs)  = handleTxHook unbalancedTxs
handleContractHook i (UtxoAtHook address)  =
    WalletEffects.startWatching address >> handleUtxoAtHook i address
handleContractHook i (OwnPubKeyHook request) = handleOwnPubKeyHook i request

handleTxHook ::
       ( Members EmulatedWalletEffects effs
       , Member (EventLogEffect ChainEvent) effs
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
    void $ runCommand saveBalancedTx WalletEventSource balancedTx
    logInfo $ "Submitting signed TX: " <> tshow signedTx
    balanceResult <- submitTx signedTx
    void $ runCommand saveBalancedTxResult NodeEventSource balanceResult

handleUtxoAtHook ::
       ( Member (Error SCBError) effs
       , Member (EventLogEffect ChainEvent) effs
       , Member (State T) effs
       , Member NodeFollowerEffect effs
       , Member ContractEffect effs
       , Members EmulatedWalletEffects effs
       )
    => FollowerID
    -> Ledger.Address
    -> Eff effs ()
handleUtxoAtHook i address = do
    logDebug $ "Fetching utxo-at: " <> tshow address
    utxoIndex <- runGlobalQuery utxoIndexProjection
    let utxoAtAddress = utxoAt utxoIndex address
    logDebug $ "Fetched utxo-at: " <> tshow utxoAtAddress
    invokeContractUpdate i $ EventPayload "utxo-at" (JSON.toJSON utxoAtAddress)

handleOwnPubKeyHook ::
       ( Member (Error SCBError) effs
       , Member (EventLogEffect ChainEvent) effs
       , Member (State T) effs
       , Member NodeFollowerEffect effs
       , Member ContractEffect effs
       , Members EmulatedWalletEffects effs
       )
    => FollowerID
    -> OwnPubKeyRequest
    -> Eff effs ()
handleOwnPubKeyHook _ NotWaitingForPubKey = pure ()
handleOwnPubKeyHook i WaitingForPubKey = do
    logInfo "Handling 'own-pubkey' hook."
    key :: WAPI.PubKey <- WAPI.ownPubKey
    invokeContractUpdate i $ EventPayload "own-pubkey" (JSON.toJSON key)

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
    ( Member Log effs
    , Member (EventLogEffect ChainEvent) effs
    )
    => UUID
    -> Eff effs ()
reportContractStatus uuid = do
    logInfo "Finding Contract"
    statuses <- runGlobalQuery latestContractStatus
    logInfo $ render $ pretty $ Map.lookup uuid statuses

lookupActiveContractState ::
    ( Member (Error SCBError) effs
    , Member (EventLogEffect ChainEvent) effs
    )
    => UUID
    -> Eff effs ActiveContractState
lookupActiveContractState uuid = do
    active <- activeContractStates
    case Map.lookup uuid active of
        Nothing -> throwError (ActiveContractStateNotFound uuid)
        Just s  -> return s

type T = (ActiveContractState, [ContractHook])

invokeContractUpdate ::
       ( Member (EventLogEffect ChainEvent) effs
       , Member (Error SCBError) effs
       , Member (State T) effs
       , Member NodeFollowerEffect effs
       , Member ContractEffect effs
       , Members EmulatedWalletEffects effs
       )
    => FollowerID
    -> Payload
    -> Eff effs ()
invokeContractUpdate i payload = do
    oldContractState <- use @T _1
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
    assign @T _1 newContractState
    pushHooks newHooks
    processAllHooks i

processAllHooks ::
       ( Members EmulatedWalletEffects effs
       , Member (Error SCBError) effs
       , Member (EventLogEffect ChainEvent) effs
       , Member (State T) effs
       , Member NodeFollowerEffect effs
       , Member ContractEffect effs
       )
    => FollowerID
    -> Eff effs ()
processAllHooks i =
    popHook i >>= \case
        Nothing -> pure ()
        Just hook -> do
            handleContractHook i hook
            sync i
            processAllHooks i

sync ::
       ( Member NodeFollowerEffect effs
       , Member (EventLogEffect ChainEvent) effs
       , Member Log effs
       )
    => FollowerID
    -> Eff effs ()
sync i = do
    blocks <- getBlocks i
    traverse_ (runCommand saveBlock NodeEventSource) blocks
    count <- runGlobalQuery blockCount
    logDebug $ "Block count is now: " <> tshow count

-- | Old hooks go to the back of the queue.
pushHooks ::
       (Member (State T) effs)
    => [ContractHook]
    -> Eff effs ()
pushHooks newHooks = modifying @T _2 (\oldHooks -> oldHooks <> newHooks)

popHook ::
       ( Member (State T) effs
       , Member Log effs
       , Member (EventLogEffect ChainEvent) effs
       , Member NodeFollowerEffect effs
       )
    => FollowerID
    -> Eff effs (Maybe ContractHook)
popHook i = do
    oldHooks <- use @T _2
    logDebug $ "Current Hooks: " <> tshow oldHooks
    case oldHooks of
        [] -> do
            sync i
            pure Nothing
        (hook:newHooks) -> do
            assign @T _2 newHooks
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
       (Member ContractEffect effs)
    => ActiveContractState
    -> Payload
    -> Eff effs PartiallyDecodedResponse
invokeContractUpdate_ ActiveContractState { activeContract = ActiveContract {activeContractPath}
                                          , partiallyDecodedResponse = PartiallyDecodedResponse {newState}
                                          } payload =
    invokeContract $
    UpdateContract activeContractPath $
    JSON.object [("oldState", newState), encodePayload payload]

installedContracts :: Member (EventLogEffect ChainEvent) effs => Eff effs (Set Contract)
installedContracts = runGlobalQuery installedContractsProjection

installedContractsProjection ::
       Projection (Set Contract) (StreamEvent key position ChainEvent)
installedContractsProjection = projectionMapMaybe contractPaths setProjection
  where
    contractPaths (StreamEvent _ _ (UserEvent (InstallContract contract))) =
        Just contract
    contractPaths _ = Nothing

activeContracts :: Member (EventLogEffect ChainEvent) effs => Eff effs (Set ActiveContract)
activeContracts = runGlobalQuery activeContractsProjection

activeContractsProjection ::
       Projection (Set ActiveContract) (StreamEvent key position ChainEvent)
activeContractsProjection = projectionMapMaybe contractPaths setProjection
  where
    contractPaths (StreamEvent _ _ (UserEvent (ContractStateTransition state))) =
        Just $ activeContract state
    contractPaths _ = Nothing

txHistory :: Member (EventLogEffect ChainEvent) effs => Eff effs [Ledger.Tx]
txHistory = runGlobalQuery txHistoryProjection

txHistoryProjection ::
       Projection [Ledger.Tx] (StreamEvent key position ChainEvent)
txHistoryProjection = projectionMapMaybe submittedTxs monoidProjection
  where
    submittedTxs (StreamEvent _ _ (NodeEvent (SubmittedTx tx))) = Just [tx]
    submittedTxs _                                              = Nothing

activeContractHistory ::
       Member (EventLogEffect ChainEvent) effs => UUID -> Eff effs [ActiveContractState]
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
       Member (EventLogEffect ChainEvent) effs => Eff effs (Map UUID ActiveContractState)
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
        , ContractEffect
        , ChainIndexEffect
        , NodeClientEffect
        , SigningProcessEffect
        , EventLogEffect ChainEvent
        , Log
        ]
