{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}

module Cardano.ChainIndex.Server(
    -- $chainIndex
    main
    , ChainIndexConfig(..)
    , ChainIndexServerMsg
    , syncState
    ) where

import           Control.Concurrent              (forkIO)
import           Control.Concurrent.MVar         (MVar, newMVar)
import           Control.Monad                   (void)
import           Control.Monad.Freer.Extras.Log
import           Control.Monad.IO.Class          (MonadIO (..))
import           Data.Function                   ((&))
import           Data.Proxy                      (Proxy (Proxy))
import           Network.HTTP.Client             (defaultManagerSettings, newManager)
import qualified Network.Wai.Handler.Warp        as Warp
import           Servant                         (Application, hoistServer, serve, (:<|>) ((:<|>)))
import           Servant.Client                  (BaseUrl (baseUrlPort), mkClientEnv)

import           Cardano.ChainIndex.API
import           Cardano.ChainIndex.Types
import           Control.Concurrent.Availability (Availability, available)
import           Data.Coerce                     (coerce)
import           Plutus.PAB.Monitoring           (runLogEffects)
import qualified Wallet.Effects                  as WalletEffects

import           Cardano.ChainIndex.ChainIndex

-- $chainIndex
-- The PAB chain index that keeps track of transaction data (UTXO set enriched
-- with datums)

app :: ChainIndexTrace -> MVar AppState -> Application
app trace stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (liftIO . processIndexEffects trace stateVar)
        (healthcheck :<|> startWatching :<|> watchedAddresses :<|> confirmedBlocks :<|> WalletEffects.transactionConfirmed :<|> WalletEffects.nextTx)

main :: ChainIndexTrace -> ChainIndexConfig -> BaseUrl -> Availability -> IO ()
main trace ChainIndexConfig{ciBaseUrl} nodeBaseUrl availability = runLogEffects trace $ do
    nodeClientEnv <- liftIO getNode
    mVarState <- liftIO $ newMVar initialAppState

    logInfo StartingNodeClientThread
    void $ liftIO $ forkIO $ runLogEffects trace $ updateThread trace 10 mVarState nodeClientEnv

    logInfo $ StartingChainIndex servicePort
    liftIO $ Warp.runSettings warpSettings $ app trace mVarState
        where
            isAvailable = available availability
            servicePort = baseUrlPort (coerce ciBaseUrl)
            warpSettings = Warp.defaultSettings & Warp.setPort servicePort & Warp.setBeforeMainLoop isAvailable
            getNode = newManager defaultManagerSettings >>= \manager -> pure $ mkClientEnv manager nodeBaseUrl
