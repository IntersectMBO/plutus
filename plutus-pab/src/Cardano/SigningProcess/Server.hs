{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TypeApplications   #-}

module Cardano.SigningProcess.Server(
    -- $signingProcess
    SigningProcessConfig(..)
    , main
    ) where

import           Control.Concurrent.Availability (Availability, available)
import           Control.Concurrent.MVar         (MVar, newMVar, putMVar, takeMVar)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error       (Error)
import qualified Control.Monad.Freer.Error       as Eff
import           Control.Monad.Freer.Extra.Log
import           Control.Monad.Freer.State       (State)
import qualified Control.Monad.Freer.State       as Eff
import           Control.Monad.IO.Class          (MonadIO (..))
import           Data.Aeson                      (FromJSON, ToJSON)
import           Data.Function                   ((&))
import           Data.Proxy                      (Proxy (..))
import           GHC.Generics                    (Generic)
import qualified Network.Wai.Handler.Warp        as Warp
import           Servant                         (Application, hoistServer, serve)
import           Servant.Client                  (BaseUrl (baseUrlPort))

import           Cardano.BM.Data.Trace           (Trace)
import           Cardano.SigningProcess.API      (API)
import           Cardano.SigningProcess.Types    (SigningProcessMsg (..))
import           Plutus.PAB.Monitoring           (runLogEffects)
import qualified Wallet.API                      as WAPI
import           Wallet.Effects                  (SigningProcessEffect)
import qualified Wallet.Effects                  as WE
import           Wallet.Emulator.Wallet          (SigningProcess, Wallet, defaultSigningProcess, handleSigningProcess)

-- $ signingProcess
-- The signing process that adds signatures to transactions.
-- WARNING: This implements 'Wallet.Emulator.SigningProcess.
-- defaultSigningProcess', which attaches the signature of a single
-- wallet to the transaction. It does not support
-- 'Wallet.Emulator.SigningProcess.signWallets', which attaches multiple
-- signatures at once. 'signWallets' is needed for the multi sig examples.

data SigningProcessConfig =
    SigningProcessConfig
        { spWallet  :: Wallet -- Wallet with whose private key transactions should be signed.
        , spBaseUrl :: BaseUrl
        } deriving stock (Eq, Show, Generic)
          deriving anyclass (ToJSON, FromJSON)

app :: MVar SigningProcess -> Application
app stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (processSigningProcessEffects stateVar)
        (uncurry WE.addSignatures)

main :: Trace IO SigningProcessMsg -> SigningProcessConfig -> Availability -> IO ()
main trace SigningProcessConfig{spWallet, spBaseUrl} availability = runLogEffects trace $ do
    stateVar <- liftIO $ newMVar (defaultSigningProcess spWallet)
    logInfo $ StartingSigningProcess servicePort
    liftIO $ Warp.runSettings warpSettings $ app stateVar
        where
            servicePort = baseUrlPort spBaseUrl
            isAvailable = available availability
            warpSettings = Warp.defaultSettings & Warp.setPort servicePort & Warp.setBeforeMainLoop isAvailable

type SigningProcessEffects =
    '[ SigningProcessEffect, State SigningProcess, Error WAPI.WalletAPIError]

processSigningProcessEffects ::
    MonadIO m
    => MVar SigningProcess
    -> Eff SigningProcessEffects a
    -> m a
processSigningProcessEffects procVar eff = do
    process <- liftIO $ takeMVar procVar
    let e = run $ Eff.runError $ Eff.runState process $ handleSigningProcess eff
    case e of
        Left err -> do
            liftIO $ putMVar procVar process
            error $ show err
        Right (a, process') -> do
            liftIO $ putMVar procVar process'
            pure a
