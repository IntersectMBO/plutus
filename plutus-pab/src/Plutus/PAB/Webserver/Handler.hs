{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Plutus.PAB.Webserver.Handler
    ( handler
    , getFullReport
    , getChainReport
    , getContractReport
    , getEvents
    , contractSchema
    ) where

import           Cardano.Metadata.Types                          (MetadataEffect, QueryResult, Subject,
                                                                  SubjectProperties (SubjectProperties), batchQuery)
import qualified Cardano.Metadata.Types                          as Metadata
import           Control.Monad.Freer                             (Eff, Member)
import           Control.Monad.Freer.Error                       (Error, throwError)
import           Control.Monad.Freer.Extra.Log                   (LogMsg, logInfo)
import qualified Data.Aeson                                      as JSON
import           Data.Map                                        (Map)
import qualified Data.Map                                        as Map
import qualified Data.Set                                        as Set
import           Data.Text                                       (Text)
import           Data.Text.Prettyprint.Doc                       (Pretty (..), defaultLayoutOptions, layoutPretty)
import           Data.Text.Prettyprint.Doc.Render.Text           (renderStrict)
import qualified Data.UUID                                       as UUID
import           Eventful                                        (streamEventEvent)
import           Language.Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription (EndpointDescription))
import           Ledger                                          (pubKeyHash)
import           Ledger.Blockchain                               (Blockchain)
import           Plutus.PAB.Core                                 (runGlobalQuery)
import qualified Plutus.PAB.Core                                 as Core
import qualified Plutus.PAB.Core.ContractInstance                as Instance
import           Plutus.PAB.Effects.Contract                     (ContractEffect, exportSchema)
import           Plutus.PAB.Effects.EventLog                     (EventLogEffect)
import           Plutus.PAB.Effects.UUID                         (UUIDEffect)
import           Plutus.PAB.Events                               (ChainEvent, ContractInstanceId (ContractInstanceId),
                                                                  ContractInstanceState (ContractInstanceState),
                                                                  csContractDefinition)
import           Plutus.PAB.PABLogMsg                            (ContractExeLogMsg (..))
import           Plutus.PAB.ParseStringifiedJSON                 (UnStringifyJSONLog, parseStringifiedJSON)
import qualified Plutus.PAB.Query                                as Query
import           Plutus.PAB.Types
import           Plutus.PAB.Webserver.Types
import           Servant                                         ((:<|>) ((:<|>)))
import           Wallet.Effects                                  (ChainIndexEffect, confirmedBlocks)
import           Wallet.Emulator.Wallet                          (Wallet (Wallet), walletPubKey)
import qualified Wallet.Rollup                                   as Rollup

healthcheck :: Monad m => m ()
healthcheck = pure ()

getContractReport ::
       forall t effs.
       ( Member (EventLogEffect (ChainEvent t)) effs
       , Member (ContractEffect t) effs
       , Ord t
       )
    => Eff effs (ContractReport t)
getContractReport = do
    installedContracts <-
        Set.toList <$> runGlobalQuery (Query.installedContractsProjection @t)
    crAvailableContracts <-
        traverse
            (\t -> ContractSignatureResponse t <$> exportSchema t)
            installedContracts
    crActiveContractStates <-
        Map.elems <$> runGlobalQuery (Query.contractState @t)
    pure ContractReport {crAvailableContracts, crActiveContractStates}

getChainReport ::
       forall effs. (Member ChainIndexEffect effs, Member MetadataEffect effs)
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

getEvents ::
       forall t effs. (Member (EventLogEffect (ChainEvent t)) effs)
    => Eff effs [ChainEvent t]
getEvents = fmap streamEventEvent <$> runGlobalQuery Query.pureProjection

getFullReport ::
       forall t effs.
       ( Member (EventLogEffect (ChainEvent t)) effs
       , Member (ContractEffect t) effs
       , Member ChainIndexEffect effs
       , Member MetadataEffect effs
       , Ord t
       )
    => Eff effs (FullReport t)
getFullReport = do
    events <- fmap streamEventEvent <$> runGlobalQuery Query.pureProjection
    contractReport <- getContractReport
    chainReport <- getChainReport
    pure FullReport {contractReport, chainReport, events}

contractSchema ::
       forall t effs.
       ( Member (EventLogEffect (ChainEvent t)) effs
       , Member (ContractEffect t) effs
       , Member (Error PABError) effs
       )
    => ContractInstanceId
    -> Eff effs (ContractSignatureResponse t)
contractSchema contractId = do
    ContractInstanceState {csContractDefinition} <-
        getContractInstanceState @t contractId
    ContractSignatureResponse csContractDefinition <$>
        exportSchema csContractDefinition

activateContract ::
       forall t effs.
       ( Member (EventLogEffect (ChainEvent t)) effs
       , Member (Error PABError) effs
       , Member (ContractEffect t) effs
       , Member UUIDEffect effs
       , Member (LogMsg (Instance.ContractInstanceMsg t)) effs
       , Ord t
       , Show t
       )
    => t
    -> Eff effs (ContractInstanceState t)
activateContract = Core.activateContract

getContractInstanceState ::
       forall t effs.
       ( Member (EventLogEffect (ChainEvent t)) effs
       , Member (Error PABError) effs
       )
    => ContractInstanceId
    -> Eff effs (ContractInstanceState t)
getContractInstanceState contractId = do
    contractStates <- runGlobalQuery (Query.contractState @t)
    case Map.lookup contractId contractStates of
        Nothing    -> throwError $ ContractInstanceNotFound contractId
        Just value -> pure value

invokeEndpoint ::
       forall t effs.
       ( Member (EventLogEffect (ChainEvent t)) effs
       , Member (LogMsg ContractExeLogMsg) effs
       , Member (Error PABError) effs
       , Member (LogMsg (Instance.ContractInstanceMsg t)) effs
       , Pretty t
       )
    => EndpointDescription
    -> JSON.Value
    -> ContractInstanceId
    -> Eff effs (ContractInstanceState t)
invokeEndpoint (EndpointDescription endpointDescription) payload contractId = do
    logInfo $ InvokingEndpoint endpointDescription payload
    newState :: [ChainEvent t] <-
        Instance.callContractEndpoint @t contractId endpointDescription payload
    logInfo $
        EndpointInvocationResponse $
        fmap
            (renderStrict . layoutPretty defaultLayoutOptions . pretty)
            newState
    getContractInstanceState contractId

parseContractId ::
       (Member (Error PABError) effs) => Text -> Eff effs ContractInstanceId
parseContractId t =
    case UUID.fromText t of
        Just uuid -> pure $ ContractInstanceId uuid
        Nothing   -> throwError $ InvalidUUIDError t

handler ::
       forall effs.
       ( Member (EventLogEffect (ChainEvent ContractExe)) effs
       , Member (ContractEffect ContractExe) effs
       , Member ChainIndexEffect effs
       , Member MetadataEffect effs
       , Member UUIDEffect effs
       , Member (LogMsg ContractExeLogMsg) effs
       , Member (Error PABError) effs
       , Member (LogMsg UnStringifyJSONLog) effs
       , Member (LogMsg (Instance.ContractInstanceMsg ContractExe)) effs
       )
    => Eff effs ()
       :<|> (Eff effs (FullReport ContractExe)
             :<|> (ContractExe -> Eff effs (ContractInstanceState ContractExe))
             :<|> (Text -> Eff effs (ContractSignatureResponse ContractExe)
                           :<|> (String -> JSON.Value -> Eff effs (ContractInstanceState ContractExe))))
handler =
    healthcheck :<|> getFullReport :<|>
    (activateContract :<|> byContractInstanceId)
  where
    byContractInstanceId rawInstanceId =
        (do instanceId <- parseContractId rawInstanceId
            contractSchema instanceId) :<|>
        handleInvokeEndpoint rawInstanceId
    handleInvokeEndpoint rawInstanceId rawEndpointDescription rawPayload = do
        instanceId <- parseContractId rawInstanceId
        payload <- parseStringifiedJSON rawPayload
        invokeEndpoint
            (EndpointDescription rawEndpointDescription)
            payload
            instanceId
