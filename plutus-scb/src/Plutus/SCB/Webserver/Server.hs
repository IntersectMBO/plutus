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
    , fullReport
    , contractSchema
    ) where

import           Control.Monad                 ((>=>))
import           Control.Monad.Except          (ExceptT (ExceptT))
import           Control.Monad.Freer           (Eff, Member)
import           Control.Monad.Freer.Error     (Error, throwError)
import           Control.Monad.Freer.Extra.Log (logInfo)
import           Control.Monad.IO.Class        (liftIO)
import           Control.Monad.Logger          (LogLevel (LevelDebug))
import           Data.Bifunctor                (first)
import qualified Data.ByteString.Lazy.Char8    as LBS
import           Data.Map                      (Map)
import qualified Data.Map                      as Map
import           Data.Proxy                    (Proxy (Proxy))
import           Data.Text                     (Text)
import qualified Data.Text.Encoding            as Text
import qualified Data.UUID                     as UUID
import           Eventful                      (streamEventEvent)
import           Ledger                        (PubKeyHash)
import           Network.Wai.Handler.Warp      (run)
import           Plutus.SCB.App                (App, runApp)
import           Plutus.SCB.Arbitrary          ()
import           Plutus.SCB.Core               (runGlobalQuery)
import           Plutus.SCB.Effects.Contract   (ContractEffect, exportSchema)
import           Plutus.SCB.Effects.EventLog   (EventLogEffect)
import           Plutus.SCB.Events             (ChainEvent, ContractInstanceId (ContractInstanceId),
                                                ContractInstanceState (ContractInstanceState), csContractDefinition)
import qualified Plutus.SCB.Query              as Query
import           Plutus.SCB.Types              (ChainOverview (ChainOverview), Config, ContractExe,
                                                SCBError (ContractInstanceNotFound, InvalidUUIDError), baseUrl,
                                                chainOverviewBlockchain, chainOverviewUnspentTxsById,
                                                chainOverviewUtxoIndex, scbWebserverConfig)
import           Plutus.SCB.Utils              (tshow)
import           Plutus.SCB.Webserver.API      (API)
import           Plutus.SCB.Webserver.Types
import           Servant                       ((:<|>) ((:<|>)), (:>), Application, Handler (Handler), err400, err500,
                                                errBody, hoistServer, serve)
import           Servant.Client                (BaseUrl (baseUrlPort))
import           Wallet.Emulator.Wallet        (Wallet)
import qualified Wallet.Rollup                 as Rollup
import           Wallet.Rollup.Types           (AnnotatedTx)

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

fullReport ::
       forall t effs. (Member (EventLogEffect (ChainEvent t)) effs)
    => Eff effs (FullReport t)
fullReport = do
    latestContractStatuses <-
        Map.elems <$> runGlobalQuery (Query.latestContractStatus @t)
    events <- fmap streamEventEvent <$> runGlobalQuery Query.pureProjection
    ChainOverview { chainOverviewBlockchain
                  , chainOverviewUnspentTxsById
                  , chainOverviewUtxoIndex
                  } <- runGlobalQuery (Query.chainOverviewProjection @t)
    let walletMap :: Map PubKeyHash Wallet = Map.empty -- TODO Will the real walletMap please step forward?
    annotatedBlockchain :: [[AnnotatedTx]] <-
        Rollup.doAnnotateBlockchain chainOverviewBlockchain
    pure
        FullReport
            { latestContractStatuses
            , events
            , transactionMap = chainOverviewUnspentTxsById
            , utxoIndex = chainOverviewUtxoIndex
            , annotatedBlockchain
            , walletMap
            }

contractSchema ::
       forall t effs.
       ( Member (EventLogEffect (ChainEvent t)) effs
       , Member (ContractEffect t) effs
       , Member (Error SCBError) effs
       )
    => ContractInstanceId
    -> Eff effs (ContractSignatureResponse t)
contractSchema contractId = do
    latestContractStatus <- runGlobalQuery (Query.latestContractStatus @t)
    case Map.lookup contractId latestContractStatus of
        Nothing -> throwError $ ContractInstanceNotFound contractId
        Just ContractInstanceState {csContractDefinition} ->
            ContractSignatureResponse <$> exportSchema csContractDefinition

parseContractId ::
       (Member (Error SCBError) effs) => Text -> Eff effs ContractInstanceId
parseContractId t = do
    let u = UUID.fromText t
    case u of
        Nothing   -> throwError $ InvalidUUIDError t
        Just uuid -> pure $ ContractInstanceId uuid

app :: Config -> Application
app config =
    serve api $
    hoistServer
        api
        (asHandler config)
        (healthcheck :<|> fullReport :<|> (parseContractId >=> contractSchema))
  where
    api = Proxy @("api" :> API ContractExe)

main :: Config -> App ()
main config = do
    let port = baseUrlPort $ baseUrl $ scbWebserverConfig config
    logInfo $ "Starting SCB backend server on port: " <> tshow port
    liftIO $ run port $ app config
