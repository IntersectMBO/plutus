{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Cardano.Wallet.MultiUserServer
    ( main
    , Config(..)
    ) where

import           Cardano.BM.Data.Trace           (Trace)
import qualified Cardano.ChainIndex.Client       as ChainIndexClient
import qualified Cardano.Node.Client             as NodeClient
import           Cardano.Wallet.API              (API)
import           Cardano.Wallet.Mock
import           Cardano.Wallet.Types            (ChainIndexUrl, Config (..), NodeUrl, WalletMsg (..), Wallets)
import           Control.Concurrent.Availability (Availability, available)
import           Control.Concurrent.MVar         (MVar, newMVar, putMVar, takeMVar)
import           Control.Monad                   ((>=>))
import qualified Control.Monad.Except            as MonadError
import           Control.Monad.Freer
import           Control.Monad.Freer.Error       (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extras      (raiseEnd)
import           Control.Monad.Freer.Extras.Log  (LogMsg, logInfo)
import           Control.Monad.Freer.State       (State, evalState, get, put, runState)
import           Control.Monad.IO.Class          (MonadIO, liftIO)
import           Crypto.PubKey.Ed25519           (secretKeySize)
import           Crypto.Random                   (getRandomBytes)
import qualified Data.ByteString.Lazy.Char8      as Char8
import           Data.Function                   ((&))
import qualified Data.Map.Strict                 as Map
import           Data.Proxy                      (Proxy (Proxy))
import           Data.Text                       (Text)
import           Network.HTTP.Client             (defaultManagerSettings, newManager)
import qualified Network.Wai.Handler.Warp        as Warp
import           Plutus.PAB.Arbitrary            ()
import           Plutus.PAB.Monitoring           (convertLog, handleLogMsgTrace, runLogEffects)
import           Servant                         (Application, Handler (Handler), NoContent (..), ServerError (..),
                                                  err400, err500, hoistServer, serve, (:<|>) ((:<|>)))
import           Servant.Client                  (BaseUrl (baseUrlPort), ClientEnv, ClientError, mkClientEnv)
import           Wallet.API                      (PubKey (..))
import qualified Wallet.API                      as WAPI
import           Wallet.Effects                  (ChainIndexEffect, NodeClientEffect, WalletEffect, ownOutputs,
                                                  ownPubKey, startWatching, submitTxn, updatePaymentWithChange,
                                                  walletSlot)
import           Wallet.Emulator.Error           (WalletAPIError)
import           Wallet.Emulator.Wallet          (WalletState, emptyWalletState)
import qualified Wallet.Emulator.Wallet          as Wallet

import           Data.Bits                       (shiftL, shiftR)
import           Data.ByteArray                  (ScrubbedBytes, unpack)
import qualified Data.ByteString                 as BS
import           Data.Map                        (Map)
import           Ledger.Crypto                   (PrivateKey (..))
import           Plutus.PAB.Monitoring           (runLogEffects)
import qualified Plutus.V1.Ledger.Bytes          as KB
import           Wallet.Effects                  (ChainIndexEffect, MultiWalletEffect (..), NodeClientEffect,
                                                  WalletEffect, createWallet, multiWallet, ownOutputs, ownPubKey,
                                                  startWatching, submitTxn, updatePaymentWithChange, walletSlot)
import           Wallet.Emulator.Error           (WalletAPIError)
import           Wallet.Emulator.NodeClient      (emptyNodeClientState)
import           Wallet.Emulator.Wallet          (SigningProcess (..), Wallet (..), WalletState (..),
                                                  defaultSigningProcess)
import qualified Wallet.Emulator.Wallet          as Wallet

type AppEffects m = '[MultiWalletEffect, NodeClientEffect, ChainIndexEffect, State Wallets, LogMsg Text, Error WalletAPIError, Error ClientError, Error ServerError, m]
newtype Seed = Seed { getSeed :: ScrubbedBytes }

generateSeed :: (LastMember m effs, MonadIO m) => Eff effs Seed
generateSeed = do
    (bytes :: ScrubbedBytes) <- sendM $ liftIO $ getRandomBytes secretKeySize
    pure $ Seed bytes


createWalletFromSeed :: Seed -> Wallet
createWalletFromSeed (Seed bytes) = let
    int = byteString2Integer . BS.pack . unpack $ bytes
    in Wallet int


-- |Helper function to convert bytestrings to integers
byteString2Integer :: BS.ByteString -> Integer
byteString2Integer = BS.foldl' (\i b -> (i `shiftL` 8) + fromIntegral b) 0
{-# INLINE byteString2Integer #-}


-- |@i2bs bitLen i@ converts @i@ to a 'ByteString' of @bitLen@ bits (must be a multiple of 8).
integer2ByteString32 :: Integer -> BS.ByteString
integer2ByteString32 i = BS.unfoldr (\l' -> if l' < 0 then Nothing else Just (fromIntegral (i `shiftR` l'), l' - 8)) (31*8)
{-# INLINE integer2ByteString32 #-}

runAppEffects ::
    ( MonadIO m
    )
    => Trace m WalletMsg
    -> ClientEnv
    -> ClientEnv
    -> Wallets
    -> Eff (AppEffects m) a
    -> m (Either ServerError (a, Wallets))
runAppEffects trace nodeClientEnv chainIndexEnv wallets action =
    handleMutliWallet action
    & NodeClient.handleNodeClientClient nodeClientEnv
    & ChainIndexClient.handleChainIndexClient chainIndexEnv
    & runState wallets
    & handleLogMsgTrace (toWalletMsg trace)
    & handleWalletApiErrors
    & handleClientErrors
    & runError
    & runM
        where
            handleWalletApiErrors = flip handleError (throwError . fromWalletAPIError)
            handleClientErrors = flip handleError (\e -> throwError $ err500 { errBody = Char8.pack (show e) })
            toWalletMsg = convertLog ChainClientMsg


handleMutliWallet :: forall m effs. ( Member NodeClientEffect effs
    , Member ChainIndexEffect effs
    , Member (State Wallets) effs
    , Member (Error WAPI.WalletAPIError) effs
    , LastMember m effs, MonadIO m
    ) => Eff (MultiWalletEffect ': effs) ~> Eff effs
handleMutliWallet = do
    interpret $ \case
        MultiWallet wid action -> do
            wallets <- get @Wallets
            case Map.lookup wid wallets of
                Just (wallet, privateKey) -> do
                    let walletState = WalletState privateKey emptyNodeClientState mempty (defaultSigningProcess wallet)
                    s <- evalState walletState $ action
                        & raiseEnd @(State WalletState ': effs)
                        & Wallet.handleWallet
                    return s
                Nothing -> throwError $ WAPI.OtherError "Wallet not found"
        CreateWallet -> do
            wallets <- get @Wallets
            Seed seed <- generateSeed
            let bytes = BS.pack . unpack $ seed
            let walletId = byteString2Integer bytes
            let wallet = Wallet walletId
            let privateKey = PrivateKey (KB.fromBytes bytes)
            let wallets' = Map.insert walletId (wallet, privateKey) wallets
            put wallets'
            return walletId

------------------------------------------------------------
-- | Run all handlers, affecting a single, global 'MVar WalletState'.
--
-- Note this code is pretty simplistic, as it makes every handler
-- block on access to a single, global 'MVar'.  We could do something
-- smarter, but I don't think it matters as this is only a mock.

asHandler ::
    Trace IO WalletMsg
    -> ClientEnv
    -> ClientEnv
    -> MVar Wallets
    -> Eff (AppEffects IO) a
    -> Handler a
asHandler trace nodeClientEnv chainIndexEnv mVarState action =
    Handler $ do
        oldState <- liftIO $ takeMVar mVarState
        result <- liftIO $ runAppEffects trace nodeClientEnv chainIndexEnv oldState action
        case result of
            Left err -> do
                liftIO $ putMVar mVarState oldState
                MonadError.throwError $ err400 { errBody = Char8.pack (show err) }
            Right (result_, newState) -> do
                liftIO $ putMVar mVarState newState
                pure result_

app :: Trace IO WalletMsg -> ClientEnv -> ClientEnv -> MVar Wallets -> Application
app trace nodeClientEnv chainIndexEnv mVarState =
    serve (Proxy @API) $
    hoistServer (Proxy @API) (asHandler trace nodeClientEnv chainIndexEnv mVarState) $
    (createWallet) :<|>
    (\w tx -> multiWallet w (submitTxn tx) >>= const (pure NoContent)) :<|> (\w -> multiWallet w ownPubKey) :<|> (\w -> multiWallet w . (uncurry updatePaymentWithChange)) :<|>
        (\w -> multiWallet w walletSlot) :<|> (\w -> multiWallet w ownOutputs)

main :: Trace IO WalletMsg -> Config -> NodeUrl -> ChainIndexUrl -> Availability -> IO ()
main trace Config {..} nodeBaseUrl chainIndexBaseUrl availability = runLogEffects trace $ do
    nodeClientEnv <- buildEnv nodeBaseUrl defaultManagerSettings
    chainIndexEnv <- buildEnv chainIndexBaseUrl defaultManagerSettings
    mVarState <- liftIO $ newMVar state
    -- runClient chainIndexEnv
    logInfo $ StartingWallet servicePort
    liftIO $ Warp.runSettings warpSettings $ app trace nodeClientEnv chainIndexEnv mVarState
    where
        servicePort = baseUrlPort baseUrl
        state = mempty
        -- state = emptyWalletState wallet
        warpSettings = Warp.defaultSettings & Warp.setPort servicePort & Warp.setBeforeMainLoop (available availability)

        buildEnv url settings = liftIO
            $ newManager settings >>= \mgr -> pure $ mkClientEnv mgr url

        {- `runClient env = liftIO
             $ runM
             $ flip handleError (error . show @ClientError)
             $ ChainIndexClient.handleChainIndexClient env
             $ startWatching (Wallet.ownAddress state)` -}
