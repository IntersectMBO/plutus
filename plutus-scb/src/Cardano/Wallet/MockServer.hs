{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Wallet.MockServer
    ( main
    ) where

import           Cardano.Wallet.API          (API)
import           Cardano.Wallet.Types        (WalletId)
import           Control.Concurrent.STM.TVar (TVar, newTVarIO, readTVarIO)
import           Control.Monad.Except        (ExceptT)
import           Control.Monad.IO.Class      (MonadIO, liftIO)
import           Control.Monad.Logger        (MonadLogger, logInfoN)
import           Control.Monad.Reader        (MonadReader, ReaderT, ask, runReaderT)
import qualified Data.ByteString.Lazy        as BSL
import           Data.Proxy                  (Proxy (Proxy))
import           Ledger                      (PubKey, Signature, Value)
import           Ledger.AddressMap           (AddressMap)
import qualified Ledger.Crypto               as Crypto
import           Network.Wai.Handler.Warp    (run)
import           Plutus.SCB.Arbitrary        ()
import           Plutus.SCB.Utils            (tshow)
import           Servant                     ((:<|>) ((:<|>)), Application, Handler (Handler), ServantErr, hoistServer,
                                              serve)
import           Servant.Extra               (capture)
import           Test.QuickCheck             (arbitrary, generate)
import           Wallet.Emulator.Wallet      (Wallet (Wallet))
import qualified Wallet.Emulator.Wallet      as EM

newtype State =
    State
        { _watchedAddresses :: AddressMap
        }
    deriving (Show, Eq)

initialState :: State
initialState = State {_watchedAddresses = mempty}

wallets :: Monad m => m [Wallet]
wallets = pure $ Wallet <$> [1 .. 10]

selectCoin :: MonadIO m => WalletId -> Value -> m ([Value], Value)
selectCoin _ target = pure ([target], mempty)

allocateAddress :: MonadIO m => WalletId -> m PubKey
allocateAddress _ = liftIO $ generate arbitrary

getOwnPubKey :: Monad m => m PubKey
getOwnPubKey = pure $ EM.walletPubKey activeWallet

activeWallet :: Wallet
activeWallet = Wallet 1

getWatchedAddresses :: (MonadIO m, MonadReader (TVar State) m) => m AddressMap
getWatchedAddresses = do
    tvarState <- ask
    State {_watchedAddresses} <- liftIO $ readTVarIO tvarState
    pure _watchedAddresses

sign :: Monad m => BSL.ByteString -> m Signature
sign bs = do
    let privK = EM.walletPrivKey activeWallet
    pure (Crypto.sign (BSL.toStrict bs) privK)

------------------------------------------------------------
asHandler ::
       TVar State -> ReaderT (TVar State) (ExceptT ServantErr IO) a -> Handler a
asHandler tvarState action = Handler (runReaderT action tvarState)

app :: TVar State -> Application
app tvarState =
    serve (Proxy @API) $
    hoistServer (Proxy @API) (asHandler tvarState) $
    wallets :<|> (getOwnPubKey :<|> sign :<|> getWatchedAddresses) :<|>
    capture (selectCoin :<|> allocateAddress)

main :: (MonadIO m, MonadLogger m) => m ()
main = do
    let port = 8081
    logInfoN $ "Starting mock wallet server on port: " <> tshow port
    tvarState <- liftIO $ newTVarIO initialState
    liftIO $ run port $ app tvarState
