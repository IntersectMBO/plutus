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
    ) where

import           Control.Monad.Except          (ExceptT (ExceptT))
import           Control.Monad.Freer           (Eff, Member)
import           Control.Monad.Freer.Extra.Log (logInfo)
import           Control.Monad.IO.Class        (liftIO)
import           Control.Monad.Logger          (LogLevel (LevelDebug))
import           Data.Bifunctor                (first)
import qualified Data.ByteString.Lazy.Char8    as LBS
import           Data.Map                      (Map)
import qualified Data.Map                      as Map
import           Data.Proxy                    (Proxy (Proxy))
import           Eventful                      (streamEventEvent)
import           Ledger                        (PubKeyHash)
import           Network.Wai.Handler.Warp      (run)
import           Plutus.SCB.App                (App, runApp)
import           Plutus.SCB.Arbitrary          ()
import           Plutus.SCB.Core               (runGlobalQuery)
import           Plutus.SCB.Effects.EventLog   (EventLogEffect)
import           Plutus.SCB.Events             (ChainEvent)
import qualified Plutus.SCB.Query              as Query
import           Plutus.SCB.Types              (ChainOverview (ChainOverview), Config, ContractExe, baseUrl,
                                                chainOverviewBlockchain, chainOverviewUnspentTxsById,
                                                chainOverviewUtxoIndex, scbWebserverConfig)
import           Plutus.SCB.Utils              (tshow)
import           Plutus.SCB.Webserver.API      (API)
import           Plutus.SCB.Webserver.Types
import           Servant                       ((:<|>) ((:<|>)), (:>), Application, Handler (Handler), err500, errBody,
                                                hoistServer, serve)
import           Servant.Client                (BaseUrl (baseUrlPort))
import           Wallet.Emulator.Wallet        (Wallet)
import qualified Wallet.Rollup                 as Rollup
import           Wallet.Rollup.Types           (AnnotatedTx)

asHandler :: Config -> App a -> Handler a
asHandler config action =
    Handler $
    ExceptT $
    fmap (first (\err -> err500 {errBody = LBS.pack $ show err})) $
    runApp LevelDebug config action

healthcheck :: Monad m => m ()
healthcheck = pure ()

fullReport :: forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs) =>
  Eff effs (FullReport t)
fullReport = do
    latestContractStatus <- runGlobalQuery (Query.latestContractStatus @t)
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
            { latestContractStatus
            , events
            , transactionMap = chainOverviewUnspentTxsById
            , utxoIndex = chainOverviewUtxoIndex
            , annotatedBlockchain
            , walletMap
            }

app :: Config -> Application
app config =
    serve api $ hoistServer api (asHandler config) $ healthcheck :<|> fullReport
  where
    api = Proxy @("api" :> API ContractExe)

main :: Config -> App ()
main config = do
    let port = baseUrlPort $ baseUrl $ scbWebserverConfig config
    logInfo $ "Starting SCB backend server on port: " <> tshow port
    liftIO $ run port $ app config
