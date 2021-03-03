{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-deprecations #-}

module Cardano.Wallet.Mock
    ( processWalletEffects
    ) where

import qualified Control.Monad.Except             as MonadError
import           Control.Monad.Freer
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.State        (runState)
import           Control.Monad.IO.Class           (MonadIO, liftIO)
import qualified Data.ByteString.Lazy             as BSL
import qualified Data.ByteString.Lazy.Char8       as BSL8
import qualified Data.ByteString.Lazy.Char8       as Char8
import           Data.Function                    ((&))
import           Data.Text.Encoding               (encodeUtf8)
import           Servant                          (ServerError (..), err400, err401, err404)
import           Servant.Client                   (ClientEnv)

import           Cardano.BM.Data.Trace            (Trace)
import qualified Cardano.ChainIndex.Client        as ChainIndexClient
import qualified Cardano.Node.Client              as NodeClient
import           Cardano.Wallet.Types             (WalletEffects, WalletMsg (..))
import           Control.Concurrent               (MVar)
import           Control.Concurrent.MVar          (putMVar, takeMVar)
import           Control.Monad.Error              (MonadError)
import           Plutus.PAB.Arbitrary             ()
import qualified Plutus.PAB.Monitoring.Monitoring as LM
import           Servant.Server                   (err500)
import           Wallet.API                       (WalletAPIError (InsufficientFunds, OtherError, PrivateKeyNotFound))
import           Wallet.Emulator.Wallet           (WalletState)
import qualified Wallet.Emulator.Wallet           as Wallet


-- | Process wallet effects. Retain state and yield HTTP400 on error
--   or set new state on success.
processWalletEffects ::
    (MonadIO m, MonadError ServerError m)
    => Trace IO WalletMsg -- ^ trace for logging
    -> ClientEnv          -- ^ node client
    -> ClientEnv          -- ^ chain index client
    -> MVar WalletState   -- ^ wallet state
    -> Eff (WalletEffects IO) a -- ^ wallet effect
    -> m a
processWalletEffects trace nodeClientEnv chainIndexEnv mVarState action = do
    oldState <- liftIO $ takeMVar mVarState
    result <- liftIO $ runWalletEffects trace nodeClientEnv chainIndexEnv oldState action
    case result of
        Left e -> do
            liftIO $ putMVar mVarState oldState
            MonadError.throwError $ err400 { errBody = Char8.pack (show e) }
        Right (result_, newState) -> do
            liftIO $ putMVar mVarState newState
            pure result_

-- | Interpret wallet effects
runWalletEffects ::
     MonadIO m
    => Trace m WalletMsg -- ^ trace for logging
    -> ClientEnv -- ^ node client
    -> ClientEnv -- ^ chain index client
    -> WalletState -- ^ current state
    -> Eff (WalletEffects m) a -- ^ wallet effect
    -> m (Either ServerError (a, WalletState))
runWalletEffects trace nodeClientEnv chainIndexEnv walletState action =
    Wallet.handleWallet action
    & interpret (NodeClient.handleNodeClientClient nodeClientEnv)
    & interpret (ChainIndexClient.handleChainIndexClient chainIndexEnv)
    & runState walletState
    & LM.handleLogMsgTrace (toWalletMsg trace)
    & handleWalletApiErrors
    & handleClientErrors
    & runError
    & runM
        where
            handleWalletApiErrors = flip handleError (throwError . fromWalletAPIError)
            handleClientErrors = flip handleError (\e -> throwError $ err500 { errBody = Char8.pack (show e) })
            toWalletMsg = LM.convertLog ChainClientMsg

-- | Convert Wallet errors to Servant error responses
fromWalletAPIError :: WalletAPIError -> ServerError
fromWalletAPIError (InsufficientFunds text) =
    err401 {errBody = BSL.fromStrict $ encodeUtf8 text}
fromWalletAPIError e@(PrivateKeyNotFound _) =
    err404 {errBody = BSL8.pack $ show e}
fromWalletAPIError (OtherError text) =
    err500 {errBody = BSL.fromStrict $ encodeUtf8 text}
