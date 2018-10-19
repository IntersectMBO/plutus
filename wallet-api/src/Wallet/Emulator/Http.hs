{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE ExplicitNamespaces         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeOperators              #-}

module Wallet.Emulator.Http
  ( app
  , initialState
  ) where

import           Control.Concurrent.STM     (STM, TVar, atomically, modifyTVar, newTVar, readTVar, readTVarIO,
                                             writeTVar)
import           Control.Monad.Error.Class  (MonadError)
import           Control.Monad.Except       (ExceptT, liftEither, runExceptT)
import           Control.Monad.IO.Class     (MonadIO, liftIO)
import           Control.Monad.Reader       (MonadReader, ReaderT, asks, runReaderT)
import           Control.Monad.State        (runStateT)
import           Control.Monad.Writer       (runWriter)
import           Control.Natural            (type (~>))
import qualified Data.ByteString.Lazy.Char8 as BSL
import qualified Data.Map                   as Map
import           Data.Maybe                 (catMaybes)
import           Data.Monoid                ((<>))
import           Data.Proxy                 (Proxy (Proxy))
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Lens.Micro                 (over, set, to)
import           Lens.Micro.Extras          (view)
import           Servant                    (Application, Handler, ServantErr (errBody), Server, err404, err500,
                                             hoistServer, serve, throwError)
import           Servant.API                ((:<|>) ((:<|>)), (:>), Capture, Get, JSON, NoContent (NoContent), Post,
                                             Put, ReqBody)
import qualified Wallet.API                 as WAPI
import           Wallet.Emulator.Types      (EmulatedWalletApi, EmulatorState (emWalletState),
                                             Notification (BlockHeight, BlockValidated), Wallet, WalletState, chain,
                                             emTxPool, emptyEmulatorState, emptyWalletState, runEmulatedWalletApi,
                                             txPool, validateEm, validationData, walletStates)
import qualified Wallet.Emulator.Types      as Types
import           Wallet.UTXO                (Block, Height, Tx, TxIn', TxOut', ValidationData, Value)

type WalletAPI
   = "wallets" :> Get '[ JSON] [Wallet]
     :<|> "wallets" :> Capture "walletid" Wallet :> Get '[ JSON] Wallet
     :<|> "wallets" :> ReqBody '[ JSON] Wallet :> Post '[ JSON] NoContent
     :<|> "wallets" :> Capture "walletid" Wallet :> "payments" :> ReqBody '[ JSON] Value :> Post '[ JSON] ( Set TxIn'
                                                                                                          , TxOut')
     :<|> "wallets" :> Capture "walletid" Wallet :> "pay-to-public-key" :> ReqBody '[ JSON] Value :> Post '[ JSON] TxOut'
     :<|> "wallets" :> Capture "walletid" Wallet :> "transactions" :> ReqBody '[ JSON] Tx :> Post '[ JSON] ()
     :<|> "wallets" :> "transactions" :> Get '[ JSON] [Tx]

type ControlAPI
   = "emulator" :> ("blockchain-actions" :> Get '[ JSON] [Tx]
                    :<|> "validation-data" :> ReqBody '[ JSON] ValidationData :> Put '[ JSON] ()
                    :<|> "wallets" :> Capture "walletid" Wallet :> "notifications" :> "block-validation" :> ReqBody '[ JSON] Block :> Post '[ JSON] ()
                    :<|> "wallets" :> Capture "walletid" Wallet :> "notifications" :> "block-height" :> ReqBody '[ JSON] Height :> Post '[ JSON] ())

type API
   = WalletAPI
     :<|> ControlAPI

newtype State = State
  { getState :: TVar EmulatorState
  }

data AppError
  = WalletAPIError WAPI.WalletAPIError
  | HttpError ServantErr

wallets ::
     (MonadError ServantErr m, MonadReader State m, MonadIO m) => m [Wallet]
wallets = do
  var <- asks getState
  ws <- liftIO $ readTVarIO var
  pure . Map.keys . emWalletState $ ws

fetchWallet ::
     (MonadError ServantErr m, MonadReader State m, MonadIO m)
  => Wallet
  -> m Wallet
fetchWallet wallet = do
  var <- asks getState
  ws <- liftIO $ readTVarIO var
  if Map.member wallet . emWalletState $ ws
    then pure wallet
    else throwError err404

createWallet :: (MonadReader State m, MonadIO m) => Wallet -> m NoContent
createWallet wallet = do
  var <- asks getState
  let walletState = emptyWalletState wallet
  liftIO . atomically $ modifyTVar var (insertWallet wallet walletState)
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
  var <- asks getState
  result <- liftIO . atomically $ runWalletApiActionSTM var wallet action a
  case result of
    Left (HttpError e) -> throwError e
    Left (WalletAPIError e) ->
      throwError $ err500 {errBody = BSL.pack . show $ e}
    Right res -> pure res

runWalletApiActionSTM ::
     TVar EmulatorState
  -> Wallet
  -> (a -> EmulatedWalletApi b)
  -> a
  -> STM (Either AppError b)
runWalletApiActionSTM var wallet action a = do
  states <- readTVar var
  let mState = Map.lookup wallet . emWalletState $ states
  case mState of
    Nothing -> pure . Left . HttpError $ err404
    Just oldState -> do
      let (res, txs) =
            runWriter .
            flip runStateT oldState . runExceptT . runEmulatedWalletApi $
            action a
      modifyTVar var (addTransactions txs)
      case res of
        (Left e, _) -> pure . Left . WalletAPIError $ e
        (Right v, newState) -> do
          modifyTVar var (insertWallet wallet newState)
          pure $ Right v

insertWallet :: Wallet -> WalletState -> EmulatorState -> EmulatorState
insertWallet w ws = over walletStates (Map.insert w ws)

addTransactions :: [Tx] -> EmulatorState -> EmulatorState
addTransactions txs = over txPool (<> txs)

getTransactions :: (MonadReader State m, MonadIO m) => m [Tx]
getTransactions = do
  var <- asks getState
  states <- liftIO $ readTVarIO var
  view (txPool . to pure) states

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

walletHandlers :: State -> Server API
walletHandlers state = hoistServer api (runM state) $ walletApi :<|> controlApi
  where
    walletApi =
      wallets :<|> fetchWallet :<|> createWallet :<|> createPaymentWithChange :<|>
      payToPublicKey :<|>
      submitTxn :<|>
      getTransactions
    controlApi =
      blockchainActions :<|> setValidationData :<|> blockValidated :<|>
      blockHeight

handleNotifications ::
     (MonadReader State m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> [Notification]
  -> m ()
handleNotifications = runWalletApiAction Types.handleNotifications

blockValidated ::
     (MonadReader State m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> Block
  -> m ()
blockValidated wallet block = handleNotifications wallet [BlockValidated block]

blockHeight ::
     (MonadReader State m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> Height
  -> m ()
blockHeight wallet height = handleNotifications wallet [BlockHeight height]

setValidationData :: (MonadReader State m, MonadIO m) => ValidationData -> m ()
setValidationData vd = do
  var <- asks getState
  liftIO . atomically $ modifyTVar var (set validationData vd)

blockchainActions :: (MonadReader State m, MonadIO m) => m [Tx]
blockchainActions = do
  var <- asks getState
  liftIO . atomically $ blockchainActionsSTM var

blockchainActionsSTM :: TVar EmulatorState -> STM [Tx]
blockchainActionsSTM var = do
  es <- readTVar var
  let processed = validateEm es <$> emTxPool es
      validated = catMaybes processed
      block = validated
      newState = addBlock block . emptyPool $ es
  writeTVar var newState
  pure block
  where
    addBlock block = over chain ((:) block)
    emptyPool = set txPool []

api :: Proxy API
api = Proxy

app :: State -> Application
app state = serve api $ walletHandlers state

initialState :: IO State
initialState = atomically $ State <$> newTVar emptyEmulatorState
