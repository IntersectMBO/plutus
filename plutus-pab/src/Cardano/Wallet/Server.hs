{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Cardano.Wallet.Server
    ( main
    ) where

import           Cardano.BM.Data.Trace            (Trace)
import qualified Cardano.ChainIndex.Client        as ChainIndexClient
import           Cardano.ChainIndex.Types         (ChainIndexUrl (..))
import           Cardano.Node.Types               (NodeUrl (..))
import           Cardano.Wallet.API               (API)
import           Cardano.Wallet.Mock
import           Cardano.Wallet.Types             (Port (..), WalletConfig (..), WalletMsg (..), WalletUrl (..),
                                                   Wallets, createWallet, multiWallet)
import           Control.Concurrent.Availability  (Availability, available)
import           Control.Concurrent.MVar          (MVar, newMVar)
import           Control.Monad                    ((>=>))
import           Control.Monad.Freer              (reinterpret, runM)
import           Control.Monad.Freer.Error        (handleError)
import           Control.Monad.Freer.Extras.Log   (logInfo)
import           Control.Monad.IO.Class           (liftIO)
import           Data.Coerce                      (coerce)
import           Data.Function                    ((&))
import           Data.Proxy                       (Proxy (Proxy))
import           Network.HTTP.Client              (defaultManagerSettings, newManager)
import qualified Network.Wai.Handler.Warp         as Warp
import           Plutus.PAB.Arbitrary             ()
import qualified Plutus.PAB.Monitoring.Monitoring as LM
import           Servant                          (Application, NoContent (..), hoistServer, serve, (:<|>) ((:<|>)))
import           Servant.Client                   (BaseUrl (baseUrlPort), ClientEnv, ClientError, mkClientEnv)
import           Wallet.Effects                   (ownOutputs, ownPubKey, startWatching, submitTxn,
                                                   updatePaymentWithChange, walletAddSignature, walletSlot)
import           Wallet.Emulator.Wallet           (WalletState, emptyWalletState)
import qualified Wallet.Emulator.Wallet           as Wallet


app :: Trace IO WalletMsg -> ClientEnv -> ClientEnv -> MVar Wallets -> Application
app trace nodeClientEnv chainIndexEnv mVarState =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (processWalletEffects trace nodeClientEnv chainIndexEnv mVarState) $
            (createWallet) :<|>
            (\w tx -> multiWallet w (submitTxn tx) >>= const (pure NoContent)) :<|>
            (\w -> multiWallet w ownPubKey) :<|>
            (\w -> multiWallet w . (uncurry updatePaymentWithChange)) :<|>
            (\w -> multiWallet w walletSlot) :<|>
            (\w -> multiWallet w ownOutputs) :<|>
            (\w tx -> multiWallet w (walletAddSignature tx))


main :: Trace IO WalletMsg -> WalletConfig -> NodeUrl -> ChainIndexUrl -> Availability -> IO ()
main trace WalletConfig { baseUrl, wallet } (NodeUrl nodeUrl) (ChainIndexUrl chainUrl) availability = LM.runLogEffects trace $ do
    nodeClientEnv <- buildEnv nodeUrl defaultManagerSettings
    chainIndexEnv <- buildEnv chainUrl defaultManagerSettings
    mVarState <- liftIO $ newMVar mempty
    runClient chainIndexEnv
    logInfo $ StartingWallet (Port servicePort)
    liftIO $ Warp.runSettings warpSettings $ app trace nodeClientEnv chainIndexEnv mVarState
    where
        servicePort = baseUrlPort (coerce baseUrl)
        warpSettings = Warp.defaultSettings & Warp.setPort servicePort & Warp.setBeforeMainLoop (available availability)

        buildEnv url settings = liftIO
            $ newManager settings >>= \mgr -> pure $ mkClientEnv mgr url

        runClient env = liftIO
             $ runM
             $ flip handleError (error . show @ClientError)
             $ reinterpret (ChainIndexClient.handleChainIndexClient env)
             $ startWatching (Wallet.ownAddress (emptyWalletState wallet))
