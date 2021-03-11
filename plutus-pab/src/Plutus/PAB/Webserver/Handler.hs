{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Plutus.PAB.Webserver.Handler
    ( handler
    , getFullReport
    , getChainReport
    , getContractReport
    , contractSchema
    , invokeEndpointSTM
    ) where

import           Cardano.Metadata.Types                           (MetadataEffect, QueryResult, Subject,
                                                                   SubjectProperties (SubjectProperties), batchQuery)
import qualified Cardano.Metadata.Types                           as Metadata
import           Control.Concurrent.STM                           (atomically)
import           Control.Monad.Freer                              (Eff, LastMember, Member, type (~>))
import           Control.Monad.Freer.Error                        (Error, throwError)
import           Control.Monad.Freer.Extras.Log                   (LogMsg, logInfo, logWarn)
import           Control.Monad.Freer.Reader                       (Reader, ask)
import           Control.Monad.IO.Class                           (MonadIO (..))
import qualified Data.Aeson                                       as JSON
import           Data.Foldable                                    (traverse_)
import           Data.Map                                         (Map)
import qualified Data.Map                                         as Map
import qualified Data.Set                                         as Set
import           Data.Text                                        (Text)
import qualified Data.UUID                                        as UUID
import           Plutus.Contract.Effects.ExposeEndpoint  (EndpointDescription (EndpointDescription))
import           Ledger                                           (pubKeyHash)
import           Ledger.Blockchain                                (Blockchain)
import qualified Plutus.PAB.Core                                  as Core
import qualified Plutus.PAB.Core.ContractInstance                 as Instance
import qualified Plutus.PAB.Core.ContractInstance.RequestHandlers as LM
import           Plutus.PAB.Core.ContractInstance.STM             (InstancesState, callEndpointOnInstance)
import           Plutus.PAB.Effects.Contract                      (ContractDefinitionStore, ContractEffect,
                                                                   ContractStore, PABContract (..), exportSchema,
                                                                   getActiveContracts, getDefinitions, getState)
import           Plutus.PAB.Effects.Contract.ContractExe          (ContractExe)
import           Plutus.PAB.Effects.UUID                          (UUIDEffect)
import           Plutus.PAB.Events.Contract                       (ContractPABRequest)
import           Plutus.PAB.Events.ContractInstanceState          (PartiallyDecodedResponse)
import           Plutus.PAB.ParseStringifiedJSON                  (UnStringifyJSONLog, parseStringifiedJSON)
import           Plutus.PAB.Types
import           Plutus.PAB.Webserver.Types
import           Servant                                          ((:<|>) ((:<|>)))
import           Wallet.Effects                                   (ChainIndexEffect, confirmedBlocks)
import           Wallet.Emulator.Wallet                           (Wallet (Wallet), walletPubKey)
import qualified Wallet.Rollup                                    as Rollup
import           Wallet.Types                                     (ContractInstanceId (..), NotificationError)

healthcheck :: Monad m => m ()
healthcheck = pure ()

getContractReport ::
       forall t effs.
       ( Member (ContractDefinitionStore t) effs
       , Member (ContractStore t) effs
       , Member (ContractEffect t) effs
       , PABContract t
       , State t ~ PartiallyDecodedResponse ContractPABRequest
       )
    => Eff effs (ContractReport (ContractDef t))
getContractReport = do
    installedContracts <- getDefinitions @t
    activeContractIDs <- fmap fst . Map.toList <$> getActiveContracts @t
    crAvailableContracts <-
        traverse
            (\t -> ContractSignatureResponse t <$> exportSchema @t t)
            installedContracts
    crActiveContractStates <- traverse (\i -> getState @t i >>= \s -> pure (i, s)) activeContractIDs
    pure ContractReport {crAvailableContracts, crActiveContractStates}

getChainReport ::
    forall effs.
    ( Member ChainIndexEffect effs
    , Member MetadataEffect effs
    )
    => Eff effs ChainReport
getChainReport = do
    blocks :: Blockchain <- confirmedBlocks
    let ChainOverview { chainOverviewBlockchain
                      , chainOverviewUnspentTxsById
                      , chainOverviewUtxoIndex
                      } = mkChainOverview blocks
    let wallets = Wallet <$> [1 .. 10]
        subjects = Metadata.toSubject . pubKeyHash . walletPubKey <$> wallets
        toMap ::
               SubjectProperties (encoding :: Metadata.JSONEncoding)
            -> Map Subject [Metadata.Property encoding]
        toMap (SubjectProperties subject properties) =
            Map.singleton subject properties
    batchQueryResult :: QueryResult (encoding :: Metadata.JSONEncoding) <-
        batchQuery
            (Metadata.QuerySubjects
                 { Metadata.subjects = Set.fromList subjects
                 , Metadata.propertyNames = Nothing
                 })
    let relatedMetadata = foldMap toMap . Metadata.results $ batchQueryResult
    annotatedBlockchain <- Rollup.doAnnotateBlockchain chainOverviewBlockchain
    pure
        ChainReport
            { transactionMap = chainOverviewUnspentTxsById
            , utxoIndex = chainOverviewUtxoIndex
            , annotatedBlockchain
            , relatedMetadata
            }

getFullReport ::
       forall t effs.
       ( Member (ContractEffect t) effs
       , Member ChainIndexEffect effs
       , Member MetadataEffect effs
       , Member (ContractDefinitionStore t) effs
       , PABContract t
       , Member (ContractStore t) effs
       , State t ~ PartiallyDecodedResponse ContractPABRequest
       )
    => Eff effs (FullReport (ContractDef t))
getFullReport = do
    contractReport <- getContractReport @t
    chainReport <- getChainReport
    pure FullReport {contractReport, chainReport}

contractSchema ::
       forall t effs.
       ( Member (ContractEffect t) effs
       , Member (Error PABError) effs
       , PABContract t
       , Member (ContractStore t) effs
       )
    => ContractInstanceId
    -> Eff effs (ContractSignatureResponse (ContractDef t))
contractSchema contractId = do
    definition <- getContractInstanceDefinition @t contractId
    ContractSignatureResponse definition <$> exportSchema @t definition

activateContract ::
       forall t m appBackend effs.
       ( Instance.AppBackendConstraints t m appBackend
       , Member (Error PABError) effs
       , Member (ContractEffect t) effs
       , Member UUIDEffect effs
       , Member (LogMsg (Instance.ContractInstanceMsg t)) effs
       , LastMember m effs
       , LastMember m (Reader ContractInstanceId ': appBackend)
       , Member (Reader InstancesState) effs
       , Member (ContractStore t) effs
       , PABContract t
       )
    => (Eff appBackend ~> IO) -- ^ How to run the @appBackend@ effects in a new thread.
    -> ContractDef t -- ^ The contract that is to be activated
    -> Eff effs ContractInstanceId
activateContract = Core.activateContractSTM @t @m @appBackend @effs

getContractInstanceDefinition ::
       forall t effs.
       ( Member (Error PABError) effs
       , Member (ContractStore t) effs
       )
    => ContractInstanceId
    -> Eff effs (ContractDef t)
getContractInstanceDefinition contractId = do
    activeContracts <- getActiveContracts @t
    case Map.lookup contractId activeContracts of
        Nothing    -> throwError $ ContractInstanceNotFound contractId
        Just value -> pure value

-- | Call an endpoint using the STM-based contract runner.
invokeEndpointSTM ::
       forall t m effs.
       ( Member (Reader InstancesState) effs
       , Member (LogMsg (Instance.ContractInstanceMsg t)) effs
       , LastMember m effs
       , MonadIO m
       )
    => EndpointDescription
    -> JSON.Value
    -> ContractInstanceId
    -> Eff effs (Maybe NotificationError)
invokeEndpointSTM d@(EndpointDescription endpointDescription) payload contractId = do
    logInfo @(LM.ContractInstanceMsg t) $ LM.CallingEndpoint endpointDescription contractId payload
    inst <- ask @InstancesState
    response <- liftIO $ atomically $ callEndpointOnInstance inst d payload contractId
    traverse_ (logWarn @(Instance.ContractInstanceMsg t) . LM.NotificationFailed) response
    pure response

parseContractId ::
       (Member (Error PABError) effs) => Text -> Eff effs ContractInstanceId
parseContractId t =
    case UUID.fromText t of
        Just uuid -> pure $ ContractInstanceId uuid
        Nothing   -> throwError $ InvalidUUIDError t

handler ::
       forall effs m appBackend.
       ( Member (ContractEffect ContractExe) effs
       , Member ChainIndexEffect effs
       , Member MetadataEffect effs
       , Member UUIDEffect effs
       , Member (Error PABError) effs
       , Member (LogMsg UnStringifyJSONLog) effs
       , Member (LogMsg (Instance.ContractInstanceMsg ContractExe)) effs
       , Instance.AppBackendConstraints ContractExe m appBackend
       , LastMember m effs
       , Member (Reader InstancesState) effs
       , Member (ContractDefinitionStore ContractExe) effs
       , Member (ContractStore ContractExe) effs
       , LastMember m (Reader ContractInstanceId ': appBackend)
       )
    => (Eff appBackend ~> IO)
    -> Eff effs ()
       :<|> (Eff effs (FullReport ContractExe)
             :<|> (ContractExe -> Eff effs ContractInstanceId)
             :<|> (Text -> Eff effs (ContractSignatureResponse ContractExe)
                           :<|> (String -> JSON.Value -> Eff effs (Maybe NotificationError))))
handler runAppBackend =
    healthcheck :<|> getFullReport @ContractExe :<|>
    (activateContract @ContractExe @m @appBackend runAppBackend :<|> byContractInstanceId)
  where
    byContractInstanceId rawInstanceId =
        (do instanceId <- parseContractId rawInstanceId
            contractSchema @ContractExe instanceId) :<|>
        handleInvokeEndpoint rawInstanceId
    handleInvokeEndpoint rawInstanceId rawEndpointDescription rawPayload = do
        instanceId <- parseContractId rawInstanceId
        payload <- parseStringifiedJSON rawPayload
        invokeEndpointSTM @ContractExe
            (EndpointDescription rawEndpointDescription)
            payload
            instanceId
