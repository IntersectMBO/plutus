{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Plutus.PAB.Webserver.Server
    ( main
    ) where

import qualified Cardano.BM.Configuration.Model                 as CM
import           Cardano.BM.Trace                               (Trace)
import           Cardano.Node.Types                             (MockServerConfig (..))
import           Control.Concurrent.Availability                (Availability, available)
import qualified Control.Concurrent.STM                         as STM
import           Control.Monad                                  ((<=<))
import           Control.Monad.Except                           (ExceptT (ExceptT))
import           Control.Monad.Freer                            (Eff, interpret)
import           Control.Monad.Freer.Reader                     (Reader, runReader)
import           Control.Monad.IO.Class                         (liftIO)
import           Data.Bifunctor                                 (first)
import qualified Data.ByteString.Lazy.Char8                     as LBS
import           Data.Function                                  ((&))
import           Data.Proxy                                     (Proxy (Proxy))
import qualified Data.Text.Encoding                             as Text
import qualified Network.Wai.Handler.Warp                       as Warp
import           Servant                                        (Application, Handler (Handler), Raw, ServerT, err400,
                                                                 err500, errBody, hoistServer, serve,
                                                                 serveDirectoryFileServer, (:<|>) ((:<|>)))
import           Servant.Client                                 (BaseUrl (baseUrlPort))


import           Control.Monad.Freer.Extras.Log                 (LogMsg, logInfo, mapLog)
import           Plutus.PAB.App                                 (App, AppBackend, runApp)
import           Plutus.PAB.Arbitrary                           ()
import           Plutus.PAB.Core.ContractInstance               (ContractInstanceMsg)
import qualified Plutus.PAB.Core.ContractInstance.BlockchainEnv as BlockchainEnv
import           Plutus.PAB.Core.ContractInstance.STM           (BlockchainEnv, InstancesState)
import qualified Plutus.PAB.Core.ContractInstance.STM           as ContractInstance
import qualified Plutus.PAB.Monitoring.PABLogMsg                as LM
import           Plutus.PAB.ParseStringifiedJSON                (UnStringifyJSONLog)
import           Plutus.PAB.Types                               (Config (..), ContractExe, PABError (InvalidUUIDError),
                                                                 baseUrl, pabWebserverConfig, staticDir)
import           Plutus.PAB.Webserver.API                       (API, WSAPI)
import           Plutus.PAB.Webserver.Handler                   (handler)
import           Plutus.PAB.Webserver.Types                     (WebSocketLogMsg)
import           Plutus.PAB.Webserver.WebSocket                 (handleWS)
import qualified Wallet.Emulator.Wallet                         as Wallet

runHandler :: InstancesState -> Trace IO LM.PABLogMsg -> CM.Configuration -> Config -> Eff (Reader InstancesState ': LogMsg LM.ContractExeLogMsg ': LogMsg (ContractInstanceMsg ContractExe) ': LogMsg WebSocketLogMsg ': LogMsg UnStringifyJSONLog ': AppBackend _) a -> IO (Either PABError a)
runHandler instancesState trace logConfig config =
  runApp trace logConfig config
      . interpret (mapLog LM.SUnstringifyJSON)
      . interpret (mapLog LM.SWebsocketMsg)
      . interpret (mapLog LM.SContractInstanceMsg)
      . interpret (mapLog LM.SContractExeLogMsg)
      . runReader instancesState

asHandler :: InstancesState -> Trace IO LM.PABLogMsg -> CM.Configuration -> Config -> Eff (Reader InstancesState ': LogMsg LM.ContractExeLogMsg ': LogMsg (ContractInstanceMsg ContractExe) ': LogMsg WebSocketLogMsg ': LogMsg UnStringifyJSONLog ': AppBackend _) a -> Handler a
asHandler instancesState trace logConfig config =
  Handler . ExceptT . fmap (first decodeErr) . runHandler instancesState trace logConfig config
  where
    decodeErr (InvalidUUIDError t) =
        err400
            {errBody = "Invalid UUID: " <> LBS.fromStrict (Text.encodeUtf8 t)}
    decodeErr err = err500 {errBody = LBS.pack $ show err}

app :: InstancesState -> BlockchainEnv -> Trace IO LM.PABLogMsg -> CM.Configuration -> Config -> Application
app instancesState env trace logConfig config = do
  let
    hdl :: forall a. Eff _ a -> IO a
    hdl = either (error . show) pure <=< runHandler instancesState trace logConfig config
            . interpret (mapLog (LM.SWalletEvent . Wallet.RequestHandlerLog))
            . interpret (mapLog (LM.SWalletEvent . Wallet.TxBalanceLog))
            . runReader env

    rest = Proxy @((API ContractExe :<|> WSAPI) :<|> Raw)
    apiServer :: ServerT (API ContractExe :<|> WSAPI) Handler
    apiServer =
      hoistServer
        (Proxy @(API ContractExe :<|> WSAPI))
        (asHandler instancesState trace logConfig config)
        (handler hdl :<|> handleWS trace logConfig)

    fileServer :: ServerT Raw Handler
    fileServer = serveDirectoryFileServer (staticDir . pabWebserverConfig $ config)
  serve rest (apiServer :<|> fileServer)


main :: Trace IO LM.PABLogMsg -> CM.Configuration -> Config -> Availability -> App ()
main trace logConfig config availability = interpret (mapLog LM.SContractExeLogMsg) $ do

    let Config{nodeServerConfig=MockServerConfig{mscSocketPath}} = config
    let port = baseUrlPort $ baseUrl $ pabWebserverConfig config
    let warpSettings :: Warp.Settings
        warpSettings = Warp.defaultSettings
            & Warp.setPort port
            & Warp.setBeforeMainLoop (available availability)
    logInfo $ LM.StartingPABBackendServer port
    instancesState <- liftIO $ STM.atomically $ ContractInstance.emptyInstancesState
    env <- liftIO $ BlockchainEnv.startNodeClient mscSocketPath instancesState
    liftIO $ Warp.runSettings warpSettings $ app instancesState env trace logConfig config
