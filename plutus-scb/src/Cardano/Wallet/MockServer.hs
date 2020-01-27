{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Wallet.MockServer where

import           Cardano.Wallet.API       (API)
import           Cardano.Wallet.Types     (WalletId)
import           Control.Monad.Except     (ExceptT)
import           Control.Monad.IO.Class   (MonadIO, liftIO)
import           Control.Monad.Logger     (MonadLogger, logInfoN)
import           Data.Proxy               (Proxy (Proxy))
import           Ledger                   (PubKey, Value)
import           Network.Wai.Handler.Warp (run)
import           Plutus.SCB.Arbitrary     ()
import           Plutus.SCB.Utils         (tshow)
import           Servant                  ((:<|>) ((:<|>)), Application, Handler (Handler), ServantErr, hoistServer,
                                           serve)
import           Servant.Extra            (capture)
import           Test.QuickCheck          (arbitrary, generate)
import           Wallet.Emulator.Wallet   (Wallet (Wallet))

wallets :: Monad m => m [Wallet]
wallets = pure $ Wallet <$> [1 .. 10]

selectCoin :: MonadIO m => WalletId -> Value -> m ([Value], Value)
selectCoin _ target = pure ([target], mempty)

allocateAddress :: MonadIO m => WalletId -> m PubKey
allocateAddress _ = liftIO $ generate arbitrary

------------------------------------------------------------
asHandler :: ExceptT ServantErr IO a -> Handler a
asHandler = Handler

app :: Application
app =
    serve (Proxy @API) $
    hoistServer (Proxy @API) asHandler $
    wallets :<|> capture (selectCoin :<|> allocateAddress)

main :: (MonadIO m, MonadLogger m) => m ()
main = do
    let port = 8081
    logInfoN $ "Starting mock wallet server on port: " <> tshow port
    liftIO $ run port app
