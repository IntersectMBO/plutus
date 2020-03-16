{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}
module Cardano.SigningProcess.Server(
    -- $signingProcess
    SigningProcessConfig(..)
    , main
    ) where

import           Control.Concurrent.MVar        (MVar, newMVar, putMVar, takeMVar)
import           Control.Monad.Freer            (Eff, run)
import           Control.Monad.Freer.Error      (Error)
import qualified Control.Monad.Freer.Error      as Eff
import           Control.Monad.Freer.State      (State)
import qualified Control.Monad.Freer.State      as Eff
import           Control.Monad.IO.Class         (MonadIO (..))
import           Control.Monad.Logger           (MonadLogger, logInfoN)
import           Data.Aeson                     (FromJSON, ToJSON)
import           Data.Proxy                     (Proxy (..))
import           GHC.Generics                   (Generic)
import qualified Network.Wai.Handler.Warp       as Warp

import           Servant                        (Application, hoistServer, serve)
import           Servant.Client                 (BaseUrl (baseUrlPort))
import qualified Wallet.API                     as WAPI
import           Wallet.Emulator.SigningProcess (SigningProcess, SigningProcessEffect)
import qualified Wallet.Emulator.SigningProcess as SP
import           Wallet.Emulator.Wallet         (Wallet)

import           Cardano.SigningProcess.API     (API)
import           Plutus.SCB.Utils               (tshow)

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
        (uncurry SP.addSignatures)

main :: (MonadIO m, MonadLogger m) => SigningProcessConfig -> m ()
main SigningProcessConfig{spWallet, spBaseUrl} = do
    stateVar <- liftIO $ newMVar (SP.defaultSigningProcess spWallet)
    let spPort = baseUrlPort spBaseUrl
    logInfoN $ "Starting signing process on port: " <> tshow spPort
    liftIO $ Warp.run spPort $ app stateVar

type SigningProcessEffects =
    '[ SigningProcessEffect, State SigningProcess, Error WAPI.WalletAPIError]

processSigningProcessEffects ::
    MonadIO m
    => MVar SigningProcess
    -> Eff SigningProcessEffects a
    -> m a
processSigningProcessEffects procVar eff = do
    process <- liftIO $ takeMVar procVar
    let e = run $ Eff.runError $ Eff.runState process $ SP.handleSigningProcess eff
    case e of
        Left err -> do
            liftIO $ putMVar procVar process
            error $ show err
        Right (a, process') -> do
            liftIO $ putMVar procVar process'
            pure a

