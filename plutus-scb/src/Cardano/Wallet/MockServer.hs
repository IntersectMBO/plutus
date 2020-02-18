{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Wallet.MockServer
    ( main
    ) where

import qualified Cardano.Node.Client            as NodeClient
import           Cardano.Wallet.API             (API)
import           Cardano.Wallet.Types           (WalletId)
import           Control.Concurrent.MVar        (MVar, newMVar, putMVar, takeMVar)
import           Control.Lens                   (makeLenses, modifying, set, use, view)
import           Control.Monad.Except           (ExceptT)
import           Control.Monad.IO.Class         (MonadIO, liftIO)
import           Control.Monad.Logger           (LoggingT, MonadLogger, logInfoN, runStderrLoggingT)
import           Control.Monad.State            (MonadState, StateT,  execStateT, get, put, runStateT)
import qualified Data.ByteString.Lazy           as BSL
import           Data.Proxy                     (Proxy (Proxy))
import           Language.Plutus.Contract.Trace (allWallets)
import           Ledger                         (Address, Blockchain, PubKey, Signature, Value)
import           Ledger.AddressMap              (AddressMap, addAddress)
import qualified Ledger.AddressMap              as AddressMap
import qualified Ledger.Crypto                  as Crypto
import           Network.HTTP.Client            (defaultManagerSettings, newManager)
import           Network.Wai.Handler.Warp       (run)
import           Plutus.SCB.Arbitrary           ()
import           Plutus.SCB.Utils               (tshow)
import           Servant                        ((:<|>) ((:<|>)), Application, Handler (Handler), NoContent (NoContent),
                                                 ServantErr, hoistServer, serve)
import           Servant.Client                 (ClientEnv, ServantError, mkClientEnv, parseBaseUrl, runClientM)
import           Servant.Extra                  (capture)
import           Test.QuickCheck                (arbitrary, generate)
import           Wallet.Emulator.Wallet         (Wallet (Wallet))
import qualified Wallet.Emulator.Wallet         as EM

newtype State =
    State
        { _watchedAddresses :: AddressMap
        }
    deriving (Show, Eq)

makeLenses 'State

initialState :: State
initialState =
    State
        { _watchedAddresses =
              foldr (addAddress . EM.walletAddress) mempty allWallets
        }

wallets :: MonadLogger m => m [Wallet]
wallets = do
    logInfoN "wallets"
    pure allWallets

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
       (MonadIO m, MonadLogger m, MonadState State m) => m AddressMap
getWatchedAddresses = do
    logInfoN "getWatchedAddresses"
    use watchedAddresses

startWatching ::
       (MonadIO m, MonadLogger m, MonadState State m) => Address -> m NoContent
startWatching address = do
    logInfoN "startWatching"
    modifying watchedAddresses (addAddress address)
    pure NoContent

sign :: MonadLogger m => BSL.ByteString -> m Signature
sign bs = do
    logInfoN "sign"
    let privK = EM.walletPrivKey activeWallet
    pure (Crypto.sign (BSL.toStrict bs) privK)

------------------------------------------------------------
-- | Synchronise the initial state.
-- At the moment, this means, "as the node for UTXOs at all our watched addresses.
syncState :: (MonadIO m, MonadState State m) => ClientEnv -> m ()
syncState nodeClientEnv = do
    oldState <- get
    result :: Either ServantError Blockchain <-
        liftIO $ runClientM NodeClient.blockchain nodeClientEnv
    case result of
        Left err -> error $ show err
        Right blockchain -> do
            let oldAddressMap = view watchedAddresses oldState
                newAddressMap =
                    foldr
                        (\block m1 ->
                             foldl
                                 (\m2 tx -> AddressMap.updateAllAddresses tx m2)
                                 m1
                                 block)
                        oldAddressMap
                        blockchain
                newState = set watchedAddresses newAddressMap oldState
            put newState

------------------------------------------------------------
-- | Run all handlers, affecting a single, global 'MVar State'.
--
-- Note this code is pretty simplistic, as it makes every handler
-- block on access to a single, global 'MVar'.  We could do something
-- smarter, but I don't think it matters as this is only a mock.
asHandler ::
       MVar State
    -> LoggingT (StateT State (ExceptT ServantErr IO)) a
    -> Handler a
asHandler mVarState action =
    Handler
        (do oldState <- liftIO $ takeMVar mVarState
            (result, newState) <- runStateT (runStderrLoggingT action) oldState
            liftIO $ putMVar mVarState newState
            pure result)

app :: MVar State -> Application
app mVarState =
    serve (Proxy @API) $
    hoistServer (Proxy @API) (asHandler mVarState) $
    wallets :<|>
    (getOwnPubKey :<|> sign :<|> getWatchedAddresses :<|> startWatching) :<|>
    capture (selectCoin :<|> allocateAddress)

main :: (MonadIO m, MonadLogger m) => m ()
main = do
    let port = 8081
    logInfoN $ "Starting mock wallet server on port: " <> tshow port
    nodeClientEnv <- mkEnv "http://localhost:8082"
    populatedState <- execStateT (syncState nodeClientEnv) initialState
    mVarState <- liftIO $ newMVar populatedState
    liftIO $ run port $ app mVarState
  where
    mkEnv baseUrl =
        liftIO $ do
            nodeManager <- newManager defaultManagerSettings
            nodeBaseUrl <- parseBaseUrl baseUrl
            pure $ mkClientEnv nodeManager nodeBaseUrl
