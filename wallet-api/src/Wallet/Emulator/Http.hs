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
  , API
  ) where

import           Control.Concurrent.STM     (STM, TVar, atomically, modifyTVar, newTVar, readTVar, readTVarIO,
                                             writeTVar)
import           Control.Monad.Error.Class  (MonadError)
import           Control.Monad.Except       (ExceptT, liftEither, runExceptT)
import           Control.Monad.IO.Class     (MonadIO, liftIO)
import           Control.Monad.Reader       (MonadReader, ReaderT, asks, runReaderT)
import           Control.Monad.State        (State, runState)
import           Control.Natural            (type (~>))
import qualified Data.ByteString.Lazy.Char8 as BSL
import qualified Data.Map                   as Map
import           Data.Maybe                 (catMaybes)
import           Data.Proxy                 (Proxy (Proxy))
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Lens.Micro                 (over, set, to)
import           Lens.Micro.Extras          (view)
import           Servant                    (Application, Handler, ServantErr (errBody), Server, err404, err500,
                                             hoistServer, serve, throwError)
import           Servant.API                ((:<|>) ((:<|>)), (:>), Capture, Get, JSON, NoContent (NoContent), Post,
                                             Put, ReqBody)
import           Wallet.API                 (KeyPair)
import qualified Wallet.API                 as WAPI
import           Wallet.Emulator.Types      (Assertion (IsValidated, OwnFundsEqual), EmulatedWalletApi,
                                             EmulatorState (emWalletState), Notification (BlockHeight, BlockValidated),
                                             Wallet, WalletState, assert, chain, emTxPool, emptyEmulatorState,
                                             emptyWalletState, liftEmulatedWallet, txPool, validateEm, validationData,
                                             walletStates)

import qualified Wallet.Emulator.Types      as Types
import           Wallet.UTXO                (Block, Height, Tx, TxIn', TxOut', ValidationData, Value)

type WalletAPI
   = "wallets" :> Get '[ JSON] [Wallet]
     :<|> "wallets" :> Capture "walletid" Wallet :> Get '[ JSON] Wallet
     :<|> "wallets" :> ReqBody '[ JSON] Wallet :> Post '[ JSON] NoContent
     :<|> "wallets" :> Capture "walletid" Wallet :> "my-key-pair" :> Get '[ JSON] KeyPair
     :<|> "wallets" :> Capture "walletid" Wallet :> "payments" :> ReqBody '[ JSON] Value :> Post '[ JSON] ( Set TxIn'
                                                                                                          , TxOut')
     :<|> "wallets" :> Capture "walletid" Wallet :> "pay-to-public-key" :> ReqBody '[ JSON] Value :> Post '[ JSON] TxOut'
     :<|> "wallets" :> Capture "walletid" Wallet :> "transactions" :> ReqBody '[ JSON] Tx :> Post '[ JSON] ()
     :<|> "wallets" :> "transactions" :> Get '[ JSON] [Tx]

type WalletControlAPI
   = "wallets" :> (Capture "walletid" Wallet :> "notifications" :> "block-validation" :> ReqBody '[ JSON] Block :> Post '[ JSON] ()
                   :<|> Capture "walletid" Wallet :> "notifications" :> "block-height" :> ReqBody '[ JSON] Height :> Post '[ JSON] ())

type AssertionsAPI
   = "assertions" :> ("own-funds-eq" :> Capture "walletid" Wallet :> ReqBody '[ JSON] Value :> Post '[ JSON] NoContent
                      :<|> "is-validated-txn" :> ReqBody '[ JSON] Tx :> Post '[ JSON] NoContent)

type ControlAPI
   = "emulator" :> ("blockchain-actions" :> Get '[ JSON] [Tx]
                    :<|> "validation-data" :> ReqBody '[ JSON] ValidationData :> Put '[ JSON] ())

type API
   = WalletAPI
     :<|> WalletControlAPI
     :<|> ControlAPI
     :<|> AssertionsAPI

newtype ServerState = ServerState
  { getState :: TVar EmulatorState
  }

wallets ::
     (MonadError ServantErr m, MonadReader ServerState m, MonadIO m)
  => m [Wallet]
wallets = do
  var <- asks getState
  ws <- liftIO $ readTVarIO var
  pure . Map.keys . emWalletState $ ws

fetchWallet ::
     (MonadError ServantErr m, MonadReader ServerState m, MonadIO m)
  => Wallet
  -> m Wallet
fetchWallet wallet = do
  var <- asks getState
  ws <- liftIO $ readTVarIO var
  if Map.member wallet . emWalletState $ ws
    then pure wallet
    else throwError err404

createWallet :: (MonadReader ServerState m, MonadIO m) => Wallet -> m NoContent
createWallet wallet = do
  var <- asks getState
  let walletState = emptyWalletState wallet
  liftIO . atomically $ modifyTVar var (insertWallet wallet walletState)
  pure NoContent

myKeyPair ::
     (MonadReader ServerState m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> m KeyPair
myKeyPair wallet = runWalletAction wallet WAPI.myKeyPair

createPaymentWithChange ::
     (MonadReader ServerState m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> Value
  -> m (Set.Set TxIn', TxOut')
createPaymentWithChange wallet =
  runWalletAction wallet . WAPI.createPaymentWithChange

payToPublicKey ::
     (MonadReader ServerState m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> Value
  -> m TxOut'
payToPublicKey wallet = runWalletAction wallet . WAPI.payToPublicKey

submitTxn ::
     (MonadReader ServerState m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> Tx
  -> m ()
submitTxn wallet = runWalletAction wallet . WAPI.submitTxn

insertWallet :: Wallet -> WalletState -> EmulatorState -> EmulatorState
insertWallet w ws = over walletStates (Map.insert w ws)

getTransactions :: (MonadReader ServerState m, MonadIO m) => m [Tx]
getTransactions = do
  var <- asks getState
  states <- liftIO $ readTVarIO var
  view (txPool . to pure) states

-- | Concrete monad stack for server server
newtype AppM a = AppM
  { unM :: ReaderT ServerState (ExceptT ServantErr IO) a
  } deriving ( Functor
             , Applicative
             , Monad
             , MonadReader ServerState
             , MonadIO
             , MonadError ServantErr
             )

runM :: ServerState -> AppM ~> Handler
runM state r = do
  res <- liftIO . runExceptT . flip runReaderT state . unM $ r
  liftEither res

walletHandlers :: ServerState -> Server API
walletHandlers state =
  hoistServer api (runM state) $
  walletApi :<|> walletControlApi :<|> controlApi :<|> assertionsApi
  where
    walletApi =
      wallets :<|> fetchWallet :<|> createWallet :<|> myKeyPair :<|> createPaymentWithChange :<|>
      payToPublicKey :<|>
      submitTxn :<|>
      getTransactions
    controlApi = blockchainActions :<|> setValidationData
    walletControlApi = blockValidated :<|> blockHeight
    assertionsApi = assertOwnFundsEq :<|> assertIsValidated

assertOwnFundsEq ::
     (MonadError ServantErr m, MonadReader ServerState m, MonadIO m)
  => Wallet
  -> Value
  -> m NoContent
assertOwnFundsEq wallet value =
  NoContent <$ (runAssertion $ OwnFundsEqual wallet value)

assertIsValidated ::
     (MonadError ServantErr m, MonadReader ServerState m, MonadIO m)
  => Tx
  -> m NoContent
assertIsValidated tx = NoContent <$ (runAssertion $ IsValidated tx)

blockValidated ::
     (MonadReader ServerState m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> Block
  -> m ()
blockValidated wallet block = handleNotifications wallet [BlockValidated block]

blockHeight ::
     (MonadReader ServerState m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> Height
  -> m ()
blockHeight wallet height = handleNotifications wallet [BlockHeight height]

runWalletAction ::
     (MonadReader ServerState m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> EmulatedWalletApi a
  -> m a
runWalletAction wallet = runServerState . fmap snd . liftEmulatedWallet wallet

runAssertion ::
     (MonadError ServantErr m, MonadReader ServerState m, MonadIO m)
  => Assertion
  -> m ()
runAssertion = runServerState . runExceptT . assert

handleNotifications ::
     (MonadReader ServerState m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> [Notification]
  -> m ()
handleNotifications wallet =
  runWalletAction wallet . Types.handleNotifications

runServerState ::
     (Show e, MonadError ServantErr m, MonadIO m, MonadReader ServerState m)
  => State EmulatorState (Either e a)
  -> m a
runServerState s = do
  var <- asks getState
  res <- liftIO . atomically . runStateSTM var $ s
  case res of
    Left e  -> throwError $ err500 {errBody = BSL.pack . show $ e}
    Right a -> pure a

runStateSTM :: TVar s -> State s ~> STM
runStateSTM var action = do
  es <- readTVar var
  let (res, newState) = runState action es
  writeTVar var newState
  pure res

setValidationData ::
     (MonadReader ServerState m, MonadIO m) => ValidationData -> m ()
setValidationData vd = do
  var <- asks getState
  liftIO . atomically $ modifyTVar var (set validationData vd)

blockchainActions :: (MonadReader ServerState m, MonadIO m) => m [Tx]
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

app :: ServerState -> Application
app state = serve api $ walletHandlers state

initialState :: IO ServerState
initialState = atomically $ ServerState <$> newTVar emptyEmulatorState
