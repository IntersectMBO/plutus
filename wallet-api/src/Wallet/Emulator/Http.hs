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
import           Control.Lens               (over, set, to, view)
import           Control.Monad.Error.Class  (MonadError)
import           Control.Monad.Except       (ExceptT, liftEither, runExceptT)
import           Control.Monad.IO.Class     (MonadIO, liftIO)
import           Control.Monad.Reader       (MonadReader, ReaderT, asks, runReaderT)
import           Control.Monad.State        (State, runState)
import           Control.Natural            (type (~>))
import qualified Data.ByteString.Lazy.Char8 as BSL
import qualified Data.Map                   as Map
import           Data.Proxy                 (Proxy (Proxy))
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Servant                    (Application, Handler, ServantErr (errBody), Server, err404, err500, err501,
                                             hoistServer, serve, throwError)
import           Servant.API                ((:<|>) ((:<|>)), (:>), Capture, Get, JSON, NoContent (NoContent), Post,
                                             ReqBody)
import           Wallet.API                 (KeyPair)
import qualified Wallet.API                 as WAPI
import           Wallet.Emulator.AddressMap (AddressMap)
import           Wallet.Emulator.Types      (Assertion (IsValidated, OwnFundsEqual),
                                             EmulatorState (_txPool, _walletStates), MockWallet,
                                             Notification (BlockValidated, CurrentSlot), Wallet, WalletState, assert,
                                             chainNewestFirst, emptyEmulatorState, emptyWalletState, liftMockWallet,
                                             txPool, walletStates)

import           Ledger                     (Address, Block, Slot, Tx, TxIn, TxOut, Value)
import qualified Wallet.Emulator.Types      as Types

type WalletAPI
   = "wallets" :> Get '[ JSON] [Wallet]
     :<|> "wallets" :> Capture "walletid" Wallet :> Get '[ JSON] Wallet
     :<|> "wallets" :> ReqBody '[ JSON] Wallet :> Post '[ JSON] NoContent
     :<|> "wallets" :> Capture "walletid" Wallet :> "my-key-pair" :> Get '[ JSON] KeyPair
     :<|> "wallets" :> Capture "walletid" Wallet :> "payments" :> ReqBody '[ JSON] Value :> Post '[ JSON] (Set TxIn, Maybe TxOut)
-- This is where the line between wallet API and control API is crossed
-- Returning the [Tx] only makes sense when running a WalletAPI m => m () inside a Trace, but not on the wallet API on its own,
--   otherwise the signature of submitTxn would be submitTxn :: Tx -> m [Tx]
-- Unfortunately we need to return the Tx here because we have to reference it later. So I can't see a way around this change.
     :<|> "wallets" :> Capture "walletid" Wallet :> "transactions" :> ReqBody '[ JSON] Tx :> Post '[ JSON] [Tx]
     :<|> "wallets" :> Capture "walletid" Wallet :> "watched-addresses" :> Get '[JSON] AddressMap
     :<|> "wallets" :> Capture "walletid" Wallet :> "watched-addresses" :> ReqBody '[JSON] Address :> Post '[JSON] NoContent
     :<|> "wallets" :> Capture "walletid" Wallet :> "current-slot" :> Get '[JSON] Slot
     :<|> "wallets" :> "transactions" :> Get '[ JSON] [Tx]

type WalletControlAPI
   = "wallets" :> (Capture "walletid" Wallet :> "notifications" :> "block-validation" :> ReqBody '[ JSON] Block :> Post '[ JSON] ()
                   :<|> Capture "walletid" Wallet :> "notifications" :> "current-slot" :> ReqBody '[ JSON] Slot :> Post '[ JSON] ())

type AssertionsAPI
   = "assertions" :> ("own-funds-eq" :> Capture "walletid" Wallet :> ReqBody '[ JSON] Value :> Post '[ JSON] NoContent
                      :<|> "is-validated-txn" :> ReqBody '[ JSON] Tx :> Post '[ JSON] NoContent)

type ControlAPI
   = "emulator" :> "blockchain-actions" :> Get '[ JSON] [Tx]

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
  pure . Map.keys . _walletStates $ ws

fetchWallet ::
     (MonadError ServantErr m, MonadReader ServerState m, MonadIO m)
  => Wallet
  -> m Wallet
fetchWallet wallet = do
  var <- asks getState
  ws <- liftIO $ readTVarIO var
  if Map.member wallet . _walletStates $ ws
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
  -> m (Set.Set TxIn, Maybe TxOut)
createPaymentWithChange wallet =
  runWalletAction wallet . WAPI.createPaymentWithChange

submitTxn ::
     (MonadReader ServerState m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> Tx
  -> m [Tx]
submitTxn wallet tx = runWalletAction wallet $ WAPI.submitTxn tx >> pure [tx]

insertWallet :: Wallet -> WalletState -> EmulatorState -> EmulatorState
insertWallet w ws = over walletStates (Map.insert w ws)

getTransactions :: (MonadReader ServerState m, MonadIO m) => m [Tx]
getTransactions = do
  var <- asks getState
  states <- liftIO $ readTVarIO var
  view (txPool . to pure) states

getWatchedAddresses :: MonadError ServantErr m
  => Wallet
  -> m AddressMap
getWatchedAddresses _ = throwError err501 -- not implemented

startWatching :: MonadError ServantErr m
  => Wallet
  -> Address
  -> m NoContent
startWatching _ _ = throwError err501 -- not implemented

getSlot :: MonadError ServantErr m
  => Wallet
  -> m Slot
getSlot _ = throwError err501 -- not implemented

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
      submitTxn :<|>
      getWatchedAddresses :<|>
      startWatching :<|>
      getSlot :<|>
      getTransactions
    controlApi = processPending
    walletControlApi = blockValidated :<|> slot
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

slot ::
     (MonadReader ServerState m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> Slot
  -> m ()
slot wallet slt = handleNotifications wallet [CurrentSlot slt]

runWalletAction ::
     (MonadReader ServerState m, MonadIO m, MonadError ServantErr m)
  => Wallet
  -> MockWallet a
  -> m a
runWalletAction wallet = runServerState . fmap snd . liftMockWallet wallet

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

processPending :: (MonadReader ServerState m, MonadIO m) => m [Tx]
processPending = do
  var <- asks getState
  liftIO . atomically $ processPendingSTM var

processPendingSTM :: TVar EmulatorState -> STM [Tx]
processPendingSTM var = do
  es <- readTVar var
  let Types.ValidatedBlock block _ rest = Types.validateBlock es (_txPool es)
      newState = addBlock block . set txPool rest $ es
  writeTVar var newState
  pure block
  where
    addBlock block = over chainNewestFirst ((:) block)

api :: Proxy API
api = Proxy

app :: ServerState -> Application
app state = serve api $ walletHandlers state

initialState :: IO ServerState
initialState = atomically $ ServerState <$> newTVar emptyEmulatorState
