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
import qualified Cardano.Protocol.Socket.Client   as Client
import           Cardano.Wallet.API               (API)
import           Cardano.Wallet.Mock
import           Cardano.Wallet.Types             (Port (..), WalletConfig (..), WalletMsg (..), WalletUrl (..),
                                                   Wallets, createWallet, multiWallet)
import           Control.Concurrent.Availability  (Availability, available)
import           Control.Concurrent.MVar          (MVar, newMVar)
import           Control.Monad.Freer              (reinterpret2, runM)
import           Control.Monad.Freer.Error        (handleError)
import           Control.Monad.Freer.Extras.Log   (logInfo)
import           Control.Monad.Freer.Reader       (runReader)
import           Control.Monad.IO.Class           (liftIO)
import           Data.Coerce                      (coerce)
import           Data.Function                    ((&))
import qualified Data.Map.Strict                  as Map
import           Data.Proxy                       (Proxy (Proxy))
import           Ledger.Tx                        (TxOut (txOutValue), TxOutTx (txOutTxOut))
import           Network.HTTP.Client              (defaultManagerSettings, newManager)
import qualified Network.Wai.Handler.Warp         as Warp
import           Plutus.PAB.Arbitrary             ()
import qualified Plutus.PAB.Monitoring.Monitoring as LM
import           Servant                          (Application, NoContent (..), hoistServer, serve, (:<|>) ((:<|>)))
import           Servant.Client                   (BaseUrl (baseUrlPort), ClientEnv, ClientError, mkClientEnv)
import           Wallet.Effects                   (ownOutputs, ownPubKey, startWatching, submitTxn,
                                                   updatePaymentWithChange, walletAddSignature, walletSlot)
import           Wallet.Emulator.Wallet           (Wallet (..), emptyWalletState)
import qualified Wallet.Emulator.Wallet           as Wallet

app :: Trace IO WalletMsg -> Client.ClientHandler -> ClientEnv -> MVar Wallets -> Application
app trace clientHandler chainIndexEnv mVarState =
    let totalFunds w = fmap (foldMap (txOutValue . txOutTxOut)) (multiWallet (Wallet w) ownOutputs) in
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (processWalletEffects trace clientHandler chainIndexEnv mVarState) $
            createWallet :<|>
            (\w tx -> multiWallet (Wallet w) (submitTxn tx) >>= const (pure NoContent)) :<|>
            (\w -> multiWallet (Wallet w) ownPubKey) :<|>
            (\w -> multiWallet (Wallet w) . uncurry updatePaymentWithChange) :<|>
            (\w -> multiWallet (Wallet w) walletSlot) :<|>
            (\w -> multiWallet (Wallet w) ownOutputs) :<|>
            totalFunds :<|>
            (\w tx -> multiWallet (Wallet w) (walletAddSignature tx))

main :: Trace IO WalletMsg -> WalletConfig -> FilePath -> ChainIndexUrl -> Availability -> IO ()
main trace WalletConfig { baseUrl, wallet } serverSocket (ChainIndexUrl chainUrl) availability = LM.runLogEffects trace $ do
    chainIndexEnv <- buildEnv chainUrl defaultManagerSettings
    let knownWallets = Map.fromList $ (\w -> (w, emptyWalletState w)) . Wallet.Wallet <$> [1..10]
    mVarState <- liftIO $ newMVar knownWallets
    clientHandler <- liftIO $ Client.runClientNode serverSocket (\_ _ -> pure ())
    runClient chainIndexEnv
    logInfo $ StartingWallet (Port servicePort)
    liftIO $ Warp.runSettings warpSettings $ app trace clientHandler chainIndexEnv mVarState
    where
        servicePort = baseUrlPort (coerce baseUrl)
        warpSettings = Warp.defaultSettings & Warp.setPort servicePort & Warp.setBeforeMainLoop (available availability)

        buildEnv url settings = liftIO
            $ newManager settings >>= \mgr -> pure $ mkClientEnv mgr url

        runClient env = liftIO
             $ runM
             $ flip handleError (error . show @ClientError)
             $ runReader env
             $ reinterpret2 (ChainIndexClient.handleChainIndexClient)
             $ startWatching (Wallet.ownAddress (emptyWalletState wallet))
