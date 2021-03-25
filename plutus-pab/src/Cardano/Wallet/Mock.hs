{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}
{-# OPTIONS_GHC -fno-warn-deprecations #-}

module Cardano.Wallet.Mock
    ( processWalletEffects
    , integer2ByteString32
    , byteString2Integer
    , newKeyPair
    ) where

import           Cardano.BM.Data.Trace            (Trace)
import qualified Cardano.ChainIndex.Client        as ChainIndexClient
import qualified Cardano.Node.Client              as NodeClient
import qualified Cardano.Protocol.Socket.Client   as Client
import           Cardano.Wallet.Types             (MultiWalletEffect (..), WalletEffects, WalletMsg (..), Wallets)
import           Control.Concurrent               (MVar)
import           Control.Concurrent.MVar          (putMVar, takeMVar)
import           Control.Lens                     (at, (.~))
import           Control.Monad.Error              (MonadError)
import qualified Control.Monad.Except             as MonadError
import           Control.Monad.Freer
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.Extras
import           Control.Monad.Freer.Reader       (runReader)
import           Control.Monad.Freer.State        (State, evalState, get, put, runState)
import           Control.Monad.IO.Class           (MonadIO, liftIO)
import           Crypto.PubKey.Ed25519            (secretKeySize)
import           Crypto.Random                    (getRandomBytes)
import           Data.Bits                        (shiftL, shiftR)
import           Data.ByteArray                   (ScrubbedBytes, unpack)
import qualified Data.ByteString                  as BS
import qualified Data.ByteString.Lazy             as BSL
import qualified Data.ByteString.Lazy.Char8       as BSL8
import qualified Data.ByteString.Lazy.Char8       as Char8
import           Data.Function                    ((&))
import qualified Data.Map                         as Map
import           Data.Text.Encoding               (encodeUtf8)
import qualified Ledger.Ada                       as Ada
import           Ledger.Crypto                    (PrivateKey (..), getPubKeyHash, privateKey2, pubKeyHash, toPublicKey)
import           Ledger.Tx                        (Tx)
import           Plutus.PAB.Arbitrary             ()
import qualified Plutus.PAB.Monitoring.Monitoring as LM
import qualified Plutus.V1.Ledger.Bytes           as KB
import           Servant                          (ServerError (..), err400, err401, err404)
import           Servant.Client                   (ClientEnv)
import           Servant.Server                   (err500)
import           Wallet.API                       (PubKey,
                                                   WalletAPIError (InsufficientFunds, OtherError, PrivateKeyNotFound))
import qualified Wallet.API                       as WAPI
import           Wallet.Effects                   (ChainIndexEffect, NodeClientEffect)
import           Wallet.Emulator.NodeClient       (emptyNodeClientState)
import           Wallet.Emulator.Wallet           (Wallet (..), WalletState (..), defaultSigningProcess)
import qualified Wallet.Emulator.Wallet           as Wallet

newtype Seed = Seed ScrubbedBytes

generateSeed :: (LastMember m effs, MonadIO m) => Eff effs Seed
generateSeed = do
    (bytes :: ScrubbedBytes) <- sendM $ liftIO $ getRandomBytes secretKeySize
    pure $ Seed bytes

-- |Helper function to convert bytestrings to integers
byteString2Integer :: BS.ByteString -> Integer
byteString2Integer = BS.foldl' (\i b -> (i `shiftL` 8) + fromIntegral b) 0
{-# INLINE byteString2Integer #-}


-- |@i2bs bitLen i@ converts @i@ to a 'ByteString' of @bitLen@ bits (must be a multiple of 8).
integer2ByteString32 :: Integer -> BS.ByteString
integer2ByteString32 i = BS.unfoldr (\l' -> if l' < 0 then Nothing else Just (fromIntegral (i `shiftR` l'), l' - 8)) (31*8)
{-# INLINE integer2ByteString32 #-}


distributeNewWalletFunds :: PubKey -> Eff '[WAPI.WalletEffect] Tx
distributeNewWalletFunds = WAPI.payToPublicKey WAPI.defaultSlotRange (Ada.adaValueOf 10000)

newKeyPair :: forall m effs. (LastMember m effs, MonadIO m) => Eff effs (PubKey, PrivateKey)
newKeyPair = do
    Seed seed <- generateSeed
    let bytes = BS.pack . unpack $ seed
    let privateKey = PrivateKey (KB.fromBytes bytes)
    let pubKey = toPublicKey privateKey
    pure (pubKey, privateKey)

-- | Handle multiple wallets using existing @Wallet.handleWallet@ handler
handleMultiWallet :: forall m effs.
    ( Member NodeClientEffect effs
    , Member ChainIndexEffect effs
    , Member (State Wallets) effs
    , Member (Error WAPI.WalletAPIError) effs
    , LastMember m effs, MonadIO m
    ) => Eff (MultiWalletEffect ': effs) ~> Eff effs
handleMultiWallet = do
    interpret $ \case
        MultiWallet wallet action -> do
            wallets <- get @Wallets
            case Map.lookup wallet wallets of
                Just walletState -> do
                    (x, newState) <- runState walletState $ action & raiseEnd & interpret Wallet.handleWallet
                    put @Wallets (wallets & at wallet .~ Just newState)
                    pure x
                Nothing -> throwError $ WAPI.OtherError "Wallet not found"
        CreateWallet -> do
            wallets <- get @Wallets
            Seed seed <- generateSeed
            let bytes = BS.pack . unpack $ seed
            let privateKey = PrivateKey (KB.fromBytes bytes)
            let pubKey = toPublicKey privateKey
            let pkh = pubKeyHash pubKey
            let walletId = byteString2Integer (getPubKeyHash pkh)
            let wallet = Wallet walletId
                newState = Wallet.emptyWalletStateFromPrivateKey privateKey
            let wallets' = Map.insert wallet newState wallets
            put wallets'
            -- For some reason this doesn't work with (Wallet 1)/privateKey1,
            -- works just fine with (Wallet 2)/privateKey2
            -- ¯\_(ツ)_/¯
            let walletState = WalletState privateKey2 emptyNodeClientState mempty (defaultSigningProcess (Wallet 2))
            _ <- evalState walletState $ interpret Wallet.handleWallet (raiseEnd $ distributeNewWalletFunds pubKey)
            return wallet


-- | Process wallet effects. Retain state and yield HTTP400 on error
--   or set new state on success.
processWalletEffects ::
    (MonadIO m, MonadError ServerError m)
    => Trace IO WalletMsg -- ^ trace for logging
    -> Client.ClientHandler -- ^ node client
    -> ClientEnv          -- ^ chain index client
    -> MVar Wallets   -- ^ wallets state
    -> Eff (WalletEffects IO) a -- ^ wallet effect
    -> m a
processWalletEffects trace clientHandler chainIndexEnv mVarState action = do
    oldState <- liftIO $ takeMVar mVarState
    result <- liftIO $ runWalletEffects trace clientHandler chainIndexEnv oldState action
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
    -> Client.ClientHandler -- ^ node client
    -> ClientEnv -- ^ chain index client
    -> Wallets -- ^ current state
    -> Eff (WalletEffects m) a -- ^ wallet effect
    -> m (Either ServerError (a, Wallets))
runWalletEffects trace clientHandler chainIndexEnv wallets action =
    handleMultiWallet action
    & reinterpret (NodeClient.handleNodeClientClient)
    & runReader clientHandler
    & reinterpret (ChainIndexClient.handleChainIndexClient)
    & runReader chainIndexEnv
    & runState wallets
    & interpret (LM.handleLogMsgTrace (toWalletMsg trace))
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
