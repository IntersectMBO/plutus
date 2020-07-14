{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Plutus.SCB.Webserver.Server
    ( main
    , getFullReport
    , contractSchema
    ) where

import           Control.Concurrent.Availability                 (Availability, available)
import           Control.Monad.Except                            (ExceptT (ExceptT))
import           Control.Monad.Freer                             (Eff, Member)
import           Control.Monad.Freer.Error                       (Error, throwError)
import           Control.Monad.Freer.Extra.Log                   (Log, logDebug, logInfo)
import           Control.Monad.IO.Class                          (liftIO)
import           Control.Monad.Logger                            (LogLevel (LevelDebug))
import qualified Data.Aeson                                      as JSON
import           Data.Bifunctor                                  (first)
import qualified Data.ByteString.Lazy.Char8                      as LBS
import           Data.Function                                   ((&))
import           Data.Map                                        (Map)
import qualified Data.Map                                        as Map
import           Data.Proxy                                      (Proxy (Proxy))
import qualified Data.Set                                        as Set
import           Data.Text                                       (Text)
import qualified Data.Text.Encoding                              as Text
import           Data.Text.Prettyprint.Doc                       (Pretty)
import qualified Data.UUID                                       as UUID
import           Eventful                                        (streamEventEvent)
import           Language.Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription (EndpointDescription))
import           Ledger                                          (PubKeyHash)
import           Ledger.Blockchain                               (Blockchain)
import qualified Network.Wai.Handler.Warp                        as Warp
import           Plutus.SCB.App                                  (App, runApp)
import           Plutus.SCB.Arbitrary                            ()
import           Plutus.SCB.Core                                 (runGlobalQuery)
import qualified Plutus.SCB.Core                                 as Core
import qualified Plutus.SCB.Core.ContractInstance                as Instance
import           Plutus.SCB.Effects.Contract                     (ContractEffect, exportSchema)
import           Plutus.SCB.Effects.EventLog                     (EventLogEffect)
import           Plutus.SCB.Effects.UUID                         (UUIDEffect)
import           Plutus.SCB.Events                               (ChainEvent, ContractInstanceId (ContractInstanceId),
                                                                  ContractInstanceState (ContractInstanceState),
                                                                  csContractDefinition)
import qualified Plutus.SCB.Query                                as Query
import           Plutus.SCB.Types                                (ChainOverview (ChainOverview), Config, ContractExe,
                                                                  SCBError (ContractInstanceNotFound, InvalidUUIDError),
                                                                  baseUrl, chainOverviewBlockchain,
                                                                  chainOverviewUnspentTxsById, chainOverviewUtxoIndex,
                                                                  mkChainOverview, scbWebserverConfig, staticDir)
import           Plutus.SCB.Utils                                (tshow)
import           Plutus.SCB.Webserver.API                        (API)
import           Plutus.SCB.Webserver.Types
import           Servant                                         ((:<|>) ((:<|>)), Application, Handler (Handler), Raw,
                                                                  err400, err500, errBody, hoistServer, serve,
                                                                  serveDirectoryFileServer)
import           Servant.Client                                  (BaseUrl (baseUrlPort))
import           Wallet.Effects                                  (ChainIndexEffect, confirmedBlocks)
import           Wallet.Emulator.Wallet                          (Wallet)
import qualified Wallet.Rollup                                   as Rollup

asHandler :: Config -> App a -> Handler a
asHandler config =
    Handler . ExceptT . fmap (first decodeErr) . runApp LevelDebug config
  where
    decodeErr (InvalidUUIDError t) =
        err400
            {errBody = "Invalid UUID: " <> LBS.fromStrict (Text.encodeUtf8 t)}
    decodeErr err = err500 {errBody = LBS.pack $ show err}

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
    installedContracts <- Set.toList <$> runGlobalQuery (Query.installedContractsProjection @t)
    crAvailableContracts <- traverse (\t -> ContractSignatureResponse t <$> exportSchema t) installedContracts
    crActiveContractStates <-
        Map.elems <$> runGlobalQuery (Query.contractState @t)
    pure ContractReport {crAvailableContracts, crActiveContractStates}

getChainReport ::
       forall t effs. Member ChainIndexEffect effs
    => Eff effs (ChainReport t)
getChainReport = do
    blocks :: Blockchain <- confirmedBlocks
    let ChainOverview { chainOverviewBlockchain
                      , chainOverviewUnspentTxsById
                      , chainOverviewUtxoIndex
                      } = mkChainOverview blocks
    let walletMap :: Map PubKeyHash Wallet = Map.empty -- TODO Will the real walletMap please step forward?
    annotatedBlockchain <- Rollup.doAnnotateBlockchain chainOverviewBlockchain
    pure
        ChainReport
            { transactionMap = chainOverviewUnspentTxsById
            , utxoIndex = chainOverviewUtxoIndex
            , annotatedBlockchain
            , walletMap
            }

getFullReport ::
       forall t effs.
       ( Member (EventLogEffect (ChainEvent t)) effs
       , Member (ContractEffect t) effs
       , Member ChainIndexEffect effs
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
       , Member (Error SCBError) effs
       )
    => ContractInstanceId
    -> Eff effs (ContractSignatureResponse t)
contractSchema contractId = do
    ContractInstanceState {csContractDefinition} <- getContractInstanceState @t contractId
    ContractSignatureResponse csContractDefinition <$> exportSchema csContractDefinition

activateContract ::
       forall t effs.
       ( Member (EventLogEffect (ChainEvent t)) effs
       , Member (Error SCBError) effs
       , Member (ContractEffect t) effs
       , Member UUIDEffect effs
       , Member Log effs
       , Ord t
       , Show t
       , Pretty t
       )
    => t
    -> Eff effs (ContractInstanceState t)
activateContract = Core.activateContract

getContractInstanceState ::
       forall t effs.
       ( Member (EventLogEffect (ChainEvent t)) effs
       , Member (Error SCBError) effs
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
       , Member (ContractEffect t) effs
       , Member Log effs
       , Member (Error SCBError) effs
       , Show t
       )
    => EndpointDescription
    -> JSON.Value
    -> ContractInstanceId
    -> Eff effs (ContractInstanceState t)
invokeEndpoint (EndpointDescription endpointDescription) payload contractId = do
    logInfo $
        "Invoking: " <> tshow endpointDescription <> " / " <> tshow payload
    newState :: [ChainEvent t] <-
        Instance.callContractEndpoint @t contractId endpointDescription payload
    logInfo $ "Invocation response: " <> tshow newState
    getContractInstanceState contractId

parseContractId ::
       (Member (Error SCBError) effs) => Text -> Eff effs ContractInstanceId
parseContractId t =
    case UUID.fromText t of
        Just uuid -> pure $ ContractInstanceId uuid
        Nothing   -> throwError $ InvalidUUIDError t

parseStringifiedJSON ::
    forall effs.
    Member Log effs
    => JSON.Value
    -> Eff effs JSON.Value
parseStringifiedJSON v = case v of
    JSON.String s -> do
        logDebug "parseStringifiedJSON: Attempting to remove 1 layer StringifyJSON"
        let s' = JSON.decode @JSON.Value $ LBS.fromStrict $ Text.encodeUtf8 s
        case s' of
            Nothing -> do
                logDebug "parseStringifiedJSON: Failed, returning original string"
                pure v
            Just s'' -> do
                logDebug "parseStringifiedJSON: Succeeded"
                pure s''
    _ -> pure v

handler ::
       forall effs.
       ( Member (EventLogEffect (ChainEvent ContractExe)) effs
       , Member (ContractEffect ContractExe) effs
       , Member ChainIndexEffect effs
       , Member UUIDEffect effs
       , Member Log effs
       , Member (Error SCBError) effs
       )
    => Eff effs ()
       :<|> (Eff effs (FullReport ContractExe)
             :<|> ((ContractExe -> Eff effs (ContractInstanceState ContractExe))
                   :<|> (Text -> Eff effs (ContractSignatureResponse ContractExe)
                                 :<|> (String -> JSON.Value -> Eff effs (ContractInstanceState ContractExe)))))
handler =
    healthcheck :<|> getFullReport :<|>
    (activateContract :<|>
     (\rawInstanceId ->
          (parseContractId rawInstanceId >>= contractSchema) :<|>
          (\rawEndpointDescription payload ->
               parseStringifiedJSON payload >>= \payload' ->
               parseContractId rawInstanceId >>=
               invokeEndpoint
                   (EndpointDescription rawEndpointDescription)
                   payload')))

app :: Config -> Application
app config = serve rest (apiServer :<|> fileServer)
  where
    rest = Proxy @(API ContractExe :<|> Raw)
    api = Proxy @(API ContractExe)
    apiServer = hoistServer api (asHandler config) handler
    fileServer = serveDirectoryFileServer (staticDir . scbWebserverConfig $ config)

main :: Config -> Availability -> App ()
main config availability = do
    let port = baseUrlPort $ baseUrl $ scbWebserverConfig config
    let warpSettings :: Warp.Settings
        warpSettings = Warp.defaultSettings & Warp.setPort port & Warp.setBeforeMainLoop (available availability)
    logInfo $ "Starting SCB backend server on port: " <> tshow port
    liftIO $ Warp.runSettings warpSettings $ app config
