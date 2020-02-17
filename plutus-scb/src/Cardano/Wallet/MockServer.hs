{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Wallet.MockServer
    ( main
    ) where

import           Cardano.Wallet.API          (API)
import           Cardano.Wallet.Types        (WalletId)
import           Control.Concurrent.STM      (atomically)
import           Control.Concurrent.STM.TVar (TVar, modifyTVar, newTVarIO, readTVarIO)
import           Control.Lens                (makeLenses, over)
import           Control.Monad.Except        (ExceptT)
import           Control.Monad.IO.Class      (MonadIO, liftIO)
import           Control.Monad.Logger        (LoggingT, MonadLogger, logInfoN, runStderrLoggingT)
import           Control.Monad.Reader        (MonadReader, ReaderT, ask, runReaderT)
import qualified Data.ByteString.Lazy        as BSL
import           Data.Proxy                  (Proxy (Proxy))
import           Ledger                      (Address, PubKey, Signature, Value)
import           Ledger.AddressMap           (AddressMap, addAddress)
import qualified Ledger.Crypto               as Crypto
import           Network.Wai.Handler.Warp    (run)
import           Plutus.SCB.Arbitrary        ()
import           Plutus.SCB.Utils            (tshow)
import           Servant                     ((:<|>) ((:<|>)), Application, Handler (Handler), NoContent (NoContent),
                                              ServantErr, hoistServer, serve)
import           Servant.Extra               (capture)
import           Test.QuickCheck             (arbitrary, generate)
import           Wallet.Emulator.Wallet      (Wallet (Wallet))
import qualified Wallet.Emulator.Wallet      as EM

newtype State =
    State
        { _watchedAddresses :: AddressMap
        }
    deriving (Show, Eq)

makeLenses 'State

initialState :: State
initialState = State {_watchedAddresses = mempty}

wallets :: MonadLogger m => m [Wallet]
wallets = do
    logInfoN "wallets"
    pure $ Wallet <$> [1 .. 10]

selectCoin :: MonadLogger m => WalletId -> Value -> m ([Value], Value)
selectCoin walletId target = do
    logInfoN "selectCoin"
    logInfoN $ "  Wallet ID: " <> tshow walletId
    logInfoN $ "     Target: " <> tshow target
    pure ([target], mempty)

allocateAddress :: (MonadIO m, MonadLogger m) => WalletId -> m PubKey
allocateAddress _ = do
    logInfoN "allocateAddress"
    liftIO $ generate arbitrary

getOwnPubKey :: MonadLogger m => m PubKey
getOwnPubKey = do
    logInfoN "getOwnPubKey"
    pure $ EM.walletPubKey activeWallet

activeWallet :: Wallet
activeWallet = Wallet 1

getWatchedAddresses ::
       (MonadIO m, MonadLogger m, MonadReader (TVar State) m) => m AddressMap
getWatchedAddresses = do
    logInfoN "getWatchedAddresses"
    tvarState <- ask
    State {_watchedAddresses} <- liftIO $ readTVarIO tvarState
    pure _watchedAddresses

startWatching ::
       (MonadIO m, MonadLogger m, MonadReader (TVar State) m)
    => Address
    -> m NoContent
startWatching address = do
    logInfoN "startWatching"
    tvarState <- ask
    liftIO $
        atomically $
        modifyTVar tvarState (over watchedAddresses (addAddress address))
    pure NoContent

sign :: MonadLogger m => BSL.ByteString -> m Signature
sign bs = do
    logInfoN "sign"
    let privK = EM.walletPrivKey activeWallet
    pure (Crypto.sign (BSL.toStrict bs) privK)

------------------------------------------------------------
asHandler ::
       TVar State
    -> LoggingT (ReaderT (TVar State) (ExceptT ServantErr IO)) a
    -> Handler a
asHandler tvarState action =
    Handler (runReaderT (runStderrLoggingT action) tvarState)

app :: TVar State -> Application
app tvarState =
    serve (Proxy @API) $
    hoistServer (Proxy @API) (asHandler tvarState) $
    wallets :<|>
    (getOwnPubKey :<|> sign :<|> getWatchedAddresses :<|> startWatching) :<|>
    capture (selectCoin :<|> allocateAddress)

main :: (MonadIO m, MonadLogger m) => m ()
main = do
    let port = 8081
    logInfoN $ "Starting mock wallet server on port: " <> tshow port
    tvarState <- liftIO $ newTVarIO initialState
    liftIO $ run port $ app tvarState
