{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE ExplicitNamespaces         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeOperators              #-}

module Wallet.Emulator.Http where

import           Control.Concurrent.STM     (STM, TVar, atomically, modifyTVar, readTVar, readTVarIO)
import           Control.Monad.Error.Class  (MonadError)
import           Control.Monad.Except       (ExceptT, liftEither, runExceptT)
import           Control.Monad.IO.Class     (MonadIO, liftIO)
import           Control.Monad.Reader       (MonadReader, ReaderT, asks, runReaderT)
import           Control.Monad.State        (runStateT)
import           Control.Monad.Writer       (runWriter)
import           Control.Natural            (type (~>))
import qualified Data.ByteString.Lazy.Char8 as BSL
import           Data.HashMap.Strict        (HashMap)
import qualified Data.HashMap.Strict        as HM
import           Data.Proxy                 (Proxy (Proxy))
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Servant                    (Application, Handler, ServantErr (errBody), Server, err404, err500, err501,
                                             hoistServer, serve, throwError)
import           Servant.API                ((:<|>) ((:<|>)), (:>), Capture, Get, JSON, NoContent (NoContent), Post,
                                             ReqBody)
import qualified Wallet.API                 as WAPI
import           Wallet.Emulator.Types      (EmulatedWalletApi, Wallet, WalletState, emptyWalletState,
                                             runEmulatedWalletApi)
import           Wallet.UTXO                (Tx, TxIn', TxOut', Value)

type WalletAPI
   = "wallets" :> Get '[ JSON] [Wallet]
     :<|> "wallets" :> Capture "walletid" Wallet :> Get '[ JSON] Wallet
     :<|> "wallets" :> ReqBody '[ JSON] Wallet :> Post '[ JSON] NoContent
     :<|> "wallets" :> Capture "walletid" Wallet :> "payments" :> ReqBody '[ JSON] Value :> Post '[ JSON] ( Set TxIn'
                                                                                                          , TxOut')
     :<|> "wallets" :> Capture "walletid" Wallet :> "pay-to-public-key" :> ReqBody '[ JSON] Value :> Post '[ JSON] TxOut'
     :<|> "wallets" :> Capture "walletid" Wallet :> "transactions" :> ReqBody '[ JSON] Tx :> Post '[ JSON] ()
     :<|> "wallets" :> "transactions" :> Get '[ JSON] [Tx]

newtype State = State
  { getWallets :: TVar (HashMap Wallet WalletState)
  }

data AppError
  = WalletAPIError WAPI.WalletAPIError
  | HttpError ServantErr

wallets ::
     (MonadError ServantErr m, MonadReader State m, MonadIO m) => m [Wallet]
wallets = do
  var <- asks getWallets
  ws <- liftIO $ readTVarIO var
  pure $ HM.keys ws

fetchWallet ::
     (MonadError ServantErr m, MonadReader State m, MonadIO m)
  => Wallet
  -> m Wallet
fetchWallet wallet = do
  var <- asks getWallets
  ws <- liftIO $ readTVarIO var
  if HM.member wallet ws
    then pure wallet
    else throwError err404

createWallet :: (MonadReader State m, MonadIO m) => Wallet -> m NoContent
createWallet wallet = do
  var <- asks getWallets
  let walletState = emptyWalletState wallet
  liftIO . atomically $ modifyTVar var (HM.insert wallet walletState)
  pure NoContent

createPaymentWithChange ::
     (MonadReader State m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> Value
  -> m (Set.Set TxIn', TxOut')
createPaymentWithChange = runWalletApiAction WAPI.createPaymentWithChange

payToPublicKey ::
     (MonadReader State m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> Value
  -> m TxOut'
payToPublicKey = runWalletApiAction WAPI.payToPublicKey

submitTxn ::
     (MonadReader State m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> Tx
  -> m ()
submitTxn = runWalletApiAction WAPI.submitTxn

runWalletApiAction ::
     (MonadReader State m, MonadIO m, MonadError ServantErr m)
  => (a -> EmulatedWalletApi b)
  -> Wallet
  -> a
  -> m b
runWalletApiAction action wallet a = do
  var <- asks getWallets
  result <- liftIO . atomically $ runWalletApiActionSTM var wallet action a
  case result of
    Left (HttpError e) -> throwError e
    Left (WalletAPIError e) ->
      throwError $ err500 {errBody = BSL.pack . show $ e}
    Right res -> pure res

runWalletApiActionSTM ::
     TVar (HashMap Wallet WalletState)
  -> Wallet
  -> (a -> EmulatedWalletApi b)
  -> a
  -> STM (Either AppError b)
runWalletApiActionSTM var wallet action a = do
  states <- readTVar var
  let mState = HM.lookup wallet states
  case mState of
    Nothing -> pure . Left . HttpError $ err404
    Just oldState -> do
      let (res, _) =
            runWriter .
            flip runStateT oldState . runExceptT . runEmulatedWalletApi $
            action a
      case res of
        (Left e, _) -> pure . Left . WalletAPIError $ e
        (Right v, newState) -> do
          modifyTVar var (HM.insert wallet newState)
          pure $ Right v

-- TODO: This will be part of the transactions API
getTransactions :: (MonadError ServantErr m) => m [Tx]
getTransactions = throwError err501

-- | Concrete monad stack for server server
newtype AppM a = AppM
  { unM :: ReaderT State (ExceptT ServantErr IO) a
  } deriving ( Functor
             , Applicative
             , Monad
             , MonadReader State
             , MonadIO
             , MonadError ServantErr
             )

runM :: State -> AppM ~> Handler
runM state r = do
  res <- liftIO . runExceptT . flip runReaderT state . unM $ r
  liftEither res

walletHandlers :: State -> Server WalletAPI
walletHandlers state =
  hoistServer walletApi (runM state) $
  wallets :<|> fetchWallet :<|> createWallet :<|> createPaymentWithChange :<|>
  payToPublicKey :<|>
  submitTxn :<|>
  getTransactions

walletApi :: Proxy WalletAPI
walletApi = Proxy

app :: State -> Application
app state = serve walletApi $ walletHandlers state
