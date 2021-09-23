{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}
{-# OPTIONS_GHC -fno-warn-deprecations #-}

module Cardano.Wallet.Mock.Handlers
    ( processWalletEffects
    , integer2ByteString32
    , byteString2Integer
    , newWallet
    , distributeNewWalletFunds
    ) where

import           Cardano.BM.Data.Trace               (Trace)
import qualified Cardano.Node.Client                 as NodeClient
import qualified Cardano.Protocol.Socket.Mock.Client as MockClient
import           Cardano.Wallet.Mock.Types           (MultiWalletEffect (..), WalletEffects, WalletInfo (..),
                                                      WalletMsg (..), Wallets, fromWalletState)
import           Control.Concurrent                  (MVar)
import           Control.Concurrent.MVar             (putMVar, takeMVar)
import           Control.Lens                        (at, (?~))
import           Control.Monad.Error                 (MonadError)
import qualified Control.Monad.Except                as MonadError
import           Control.Monad.Freer
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.Extras
import           Control.Monad.Freer.Reader          (runReader)
import           Control.Monad.Freer.State           (State, evalState, get, put, runState)
import           Control.Monad.IO.Class              (MonadIO, liftIO)
import           Crypto.Random                       (getRandomBytes)
import           Data.Bits                           (shiftL, shiftR)
import           Data.ByteArray                      (ScrubbedBytes, unpack)
import qualified Data.ByteString                     as BS
import qualified Data.ByteString.Lazy                as BSL
import qualified Data.ByteString.Lazy.Char8          as BSL8
import qualified Data.ByteString.Lazy.Char8          as Char8
import           Data.Function                       ((&))
import qualified Data.Map                            as Map
import           Data.Text.Encoding                  (encodeUtf8)
import           Data.Text.Prettyprint.Doc           (pretty)
import qualified Ledger.Ada                          as Ada
import           Ledger.Crypto                       (PubKeyHash, generateFromSeed, privateKey2, pubKeyHash,
                                                      toPublicKey)
import           Ledger.Fee                          (FeeConfig)
import           Ledger.TimeSlot                     (SlotConfig)
import           Ledger.Tx                           (Tx)
import           Plutus.ChainIndex                   (ChainIndexQueryEffect)
import qualified Plutus.ChainIndex.Client            as ChainIndex
import           Plutus.PAB.Arbitrary                ()
import qualified Plutus.PAB.Monitoring.Monitoring    as LM
import           Servant                             (ServerError (..), err400, err401, err404)
import           Servant.Client                      (ClientEnv)
import           Servant.Server                      (err500)
import           Wallet.API                          (PubKey, WalletAPIError (..))
import qualified Wallet.API                          as WAPI
import           Wallet.Effects                      (NodeClientEffect)
import           Wallet.Emulator.LogMessages         (TxBalanceMsg)
import           Wallet.Emulator.NodeClient          (emptyNodeClientState)
import           Wallet.Emulator.Wallet              (Wallet, WalletState (..), defaultSigningProcess, knownWallet)
import qualified Wallet.Emulator.Wallet              as Wallet

newtype Seed = Seed ScrubbedBytes

generateSeed :: (LastMember m effs, MonadIO m) => Eff effs Seed
generateSeed = do
    (bytes :: ScrubbedBytes) <- sendM $ liftIO $ getRandomBytes 32
    pure $ Seed bytes

{-# INLINE byteString2Integer #-}
-- |Helper function to convert bytestrings to integers
byteString2Integer :: BS.ByteString -> Integer
byteString2Integer = BS.foldl' (\i b -> (i `shiftL` 8) + fromIntegral b) 0

{-# INLINE integer2ByteString32 #-}
-- |@i2bs bitLen i@ converts @i@ to a 'ByteString' of @bitLen@ bits (must be a multiple of 8).
integer2ByteString32 :: Integer -> BS.ByteString
integer2ByteString32 i = BS.unfoldr (\l' -> if l' < 0 then Nothing else Just (fromIntegral (i `shiftR` l'), l' - 8)) (31*8)

distributeNewWalletFunds :: forall effs. (Member WAPI.WalletEffect effs, Member (Error WalletAPIError) effs) => PubKeyHash -> Eff effs Tx
distributeNewWalletFunds = WAPI.payToPublicKeyHash WAPI.defaultSlotRange (Ada.adaValueOf 10000)

newWallet :: forall m effs. (LastMember m effs, MonadIO m) => Eff effs (Wallet, WalletState, PubKey)
newWallet = do
    Seed seed <- generateSeed
    let secretKeyBytes = BS.pack . unpack $ seed
    let privateKey = generateFromSeed secretKeyBytes
    pure (Wallet.Wallet (Wallet.MockWallet privateKey), Wallet.emptyWalletState privateKey, toPublicKey privateKey)

-- | Handle multiple wallets using existing @Wallet.handleWallet@ handler
handleMultiWallet :: forall m effs.
    ( Member NodeClientEffect effs
    , Member ChainIndexQueryEffect effs
    , Member (State Wallets) effs
    , Member (Error WAPI.WalletAPIError) effs
    , Member (LogMsg WalletMsg) effs
    , LastMember m effs
    , MonadIO m
    )
    => FeeConfig
    -> MultiWalletEffect ~> Eff effs
handleMultiWallet feeCfg = \case
    MultiWallet wallet action -> do
        wallets <- get @Wallets
        case Map.lookup wallet wallets of
            Just walletState -> do
                (x, newState) <- runState walletState
                    $ action
                        & raiseEnd
                        & interpret (Wallet.handleWallet feeCfg)
                        & interpret (mapLog @TxBalanceMsg @WalletMsg Balancing)
                put @Wallets (wallets & at wallet ?~ newState)
                pure x
            Nothing -> throwError $ WAPI.OtherError "Wallet not found"
    CreateWallet -> do
        wallets <- get @Wallets
        (wallet, newState, pubKey) <- newWallet
        let wallets' = Map.insert wallet newState wallets
        put wallets'
        -- For some reason this doesn't work with (Wallet 1)/privateKey1,
        -- works just fine with (Wallet 2)/privateKey2
        -- ¯\_(ツ)_/¯
        let walletState = WalletState privateKey2 emptyNodeClientState mempty (defaultSigningProcess (knownWallet 2))
        _ <- evalState walletState $
            interpret (mapLog @TxBalanceMsg @WalletMsg Balancing)
            $ interpret (Wallet.handleWallet feeCfg)
            $ distributeNewWalletFunds
            $ Wallet.walletPubKeyHash wallet
        return $ WalletInfo{wiWallet = wallet, wiPubKey = Just pubKey, wiPubKeyHash = pubKeyHash pubKey}
    GetWalletInfo wllt -> do
        wallets <- get @Wallets
        return $ fmap fromWalletState $ Map.lookup (Wallet.Wallet wllt) wallets

-- | Process wallet effects. Retain state and yield HTTP400 on error
--   or set new state on success.
processWalletEffects ::
    (MonadIO m, MonadError ServerError m)
    => Trace IO WalletMsg -- ^ trace for logging
    -> MockClient.TxSendHandle -- ^ node client
    -> NodeClient.ChainSyncHandle -- ^ node client
    -> ClientEnv          -- ^ chain index client
    -> MVar Wallets   -- ^ wallets state
    -> FeeConfig
    -> SlotConfig
    -> Eff (WalletEffects IO) a -- ^ wallet effect
    -> m a
processWalletEffects trace txSendHandle chainSyncHandle chainIndexEnv mVarState feeCfg slotCfg action = do
    oldState <- liftIO $ takeMVar mVarState
    result <- liftIO $ runWalletEffects trace
                                        txSendHandle
                                        chainSyncHandle
                                        chainIndexEnv
                                        oldState
                                        feeCfg
                                        slotCfg
                                        action
    case result of
        Left e -> do
            liftIO $ putMVar mVarState oldState
            MonadError.throwError $ err400 { errBody = Char8.pack (show e) }
        Right (result_, newState) -> do
            liftIO $ putMVar mVarState newState
            pure result_

-- | Interpret wallet effects
runWalletEffects ::
    Trace IO WalletMsg -- ^ trace for logging
    -> MockClient.TxSendHandle -- ^ node client
    -> NodeClient.ChainSyncHandle -- ^ node client
    -> ClientEnv -- ^ chain index client
    -> Wallets -- ^ current state
    -> FeeConfig
    -> SlotConfig
    -> Eff (WalletEffects IO) a -- ^ wallet effect
    -> IO (Either ServerError (a, Wallets))
runWalletEffects trace txSendHandle chainSyncHandle chainIndexEnv wallets feeCfg slotCfg action =
    reinterpret (handleMultiWallet feeCfg) action
    & interpret (LM.handleLogMsgTrace trace)
    & reinterpret2 (NodeClient.handleNodeClientClient slotCfg)
    & runReader chainSyncHandle
    & runReader txSendHandle
    & reinterpret ChainIndex.handleChainIndexClient
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
fromWalletAPIError e@(ValidationError _) =
    err500 {errBody = BSL8.pack $ show $ pretty e}
fromWalletAPIError (OtherError text) =
    err500 {errBody = BSL.fromStrict $ encodeUtf8 text}
