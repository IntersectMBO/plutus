{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}

module Cardano.Wallet.Server
    ( main
    ) where

import           Control.Monad                    ((>=>))
import           Control.Monad.Freer              (reinterpret, runM)
import           Control.Monad.Freer.Error        (handleError)
import           Control.Monad.Freer.Extras.Log   (logInfo)
import           Control.Monad.IO.Class           (liftIO)
import           Data.Function                    ((&))
import           Data.Proxy                       (Proxy (Proxy))
import           Network.HTTP.Client              (defaultManagerSettings, newManager)
import qualified Network.Wai.Handler.Warp         as Warp
import           Servant                          (Application, NoContent (..), hoistServer, serve, (:<|>) ((:<|>)))
import           Servant.Client                   (BaseUrl (baseUrlPort), ClientEnv, ClientError, mkClientEnv)


import           Cardano.BM.Data.Trace            (Trace)
import qualified Cardano.ChainIndex.Client        as ChainIndexClient
import           Cardano.ChainIndex.Types         (ChainIndexUrl (..))
import           Cardano.Node.Types               (NodeUrl (..))
import           Cardano.Wallet.API               (API)
import           Cardano.Wallet.Mock
import           Cardano.Wallet.Types             (Port (..), WalletConfig (..), WalletMsg (..), WalletUrl (..))
import           Control.Concurrent.Availability  (Availability, available)
import           Control.Concurrent.MVar          (MVar, newMVar)
import           Data.Coerce                      (coerce)
import           Plutus.PAB.Arbitrary             ()
import qualified Plutus.PAB.Monitoring.Monitoring as LM
import           Wallet.Effects                   (ownOutputs, ownPubKey, startWatching, submitTxn,
                                                   updatePaymentWithChange, walletSlot)
import           Wallet.Emulator.Wallet           (WalletState, emptyWalletState)
import qualified Wallet.Emulator.Wallet           as Wallet




app :: Trace IO WalletMsg -> ClientEnv -> ClientEnv -> MVar WalletState -> Application
app trace nodeClientEnv chainIndexEnv mVarState =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (processWalletEffects trace nodeClientEnv chainIndexEnv mVarState)
         ((submitTxn >=> const (pure NoContent)) :<|> ownPubKey :<|> uncurry updatePaymentWithChange :<|>
          walletSlot :<|> ownOutputs)

main :: Trace IO WalletMsg -> WalletConfig -> NodeUrl -> ChainIndexUrl -> Availability -> IO ()
main trace WalletConfig { baseUrl, wallet } (NodeUrl nodeUrl) (ChainIndexUrl chainUrl) availability = LM.runLogEffects trace $ do
    nodeClientEnv <- buildEnv nodeUrl defaultManagerSettings
    chainIndexEnv <- buildEnv chainUrl defaultManagerSettings
    mVarState <- liftIO $ newMVar state
    runClient chainIndexEnv
    logInfo $ StartingWallet (Port servicePort)
    liftIO $ Warp.runSettings warpSettings $ app trace nodeClientEnv chainIndexEnv mVarState
    where
        servicePort = baseUrlPort (coerce baseUrl)
        state = emptyWalletState wallet
        warpSettings = Warp.defaultSettings & Warp.setPort servicePort & Warp.setBeforeMainLoop (available availability)

        buildEnv url settings = liftIO
            $ newManager settings >>= \mgr -> pure $ mkClientEnv mgr url

        runClient env = liftIO
             $ runM
             $ flip handleError (error . show @ClientError)
             $ reinterpret (ChainIndexClient.handleChainIndexClient env)
             $ startWatching (Wallet.ownAddress state)
