{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Server where

import           API                               (API, PrivateKey, PublicKey, RawHtml (..))
import           Control.Exception                 (throwIO)
import           Control.Monad.Except              (ExceptT)
import           Control.Monad.IO.Class            (MonadIO, liftIO)
import           Control.Monad.Logger              (LoggingT, MonadLogger, logInfoN, runStderrLoggingT)
import           Control.Monad.Reader              (ReaderT, runReaderT)
import qualified Crypto.Hash.SHA256                as SHA256
import           Data.Aeson                        (FromJSON, ToJSON, eitherDecode, encode)
import           Data.Aeson                        as Aeson
import qualified Data.ByteString                   as BS
import qualified Data.ByteString.Base16            as B16
import qualified Data.ByteString.Lazy              as BSL
import qualified Data.ByteString.Lazy.UTF8         as BSLU
import qualified Data.ByteString.UTF8              as BSU
import           Data.Pool                         (Pool, withResource)
import           Data.Proxy                        (Proxy (Proxy))
import           Data.String                       as S
import           Data.Text                         (Text)
import qualified Data.Text                         as Text
import           Database.PostgreSQL.Simple        (Connection, Only (..), SqlError, execute)
import           Database.PostgreSQL.Simple.Errors (ConstraintViolation (..), catchViolation)
import           Database.PostgreSQL.Simple.SqlQQ  (sql)
import           GHC.Generics                      (Generic)
import           Network.Wai.Middleware.Cors       (cors, corsRequestHeaders, simpleCorsResourcePolicy)
import           Servant                           (Application, Handler (Handler), Server, ServerError, hoistServer,
                                                    serve, serveDirectoryFileServer, throwError, (:<|>) ((:<|>)), (:>))

handlers :: Pool Connection -> FilePath -> Server API
handlers conns staticPath = createWallet conns :<|>
                            (showResult . createWallet conns) :<|>
                            testEndpoint :<|>
                            serveDirectoryFileServer staticPath

showResult :: Show a => Handler a -> Handler String
showResult handler = do x <- handler
                        pure (show x)

-- Creates a Wallet with 1000 ADA
createWallet :: Pool Connection -> PrivateKey -> Handler PublicKey
createWallet conns privateKey =
  liftIO . withResource conns $ \conn -> do
    catchViolation catcher $ do
      execute conn
        [sql|WITH mc_insert AS (INSERT INTO money_container DEFAULT VALUES
                                RETURNING money_container_id AS id),
                  wallet_insert AS (INSERT INTO wallet (money_container_id, pub_key)
                                    VALUES ((SELECT id FROM mc_insert), ?))
              INSERT INTO currency_amount (amount, money_container_id, currency_symbol, token_name)
              VALUES (1000000000, (SELECT id FROM mc_insert), '', '')|] [publicKey]
      pure publicKey
  where
    publicKey = BSU.toString $ B16.encode $ SHA256.hash $ BSU.fromString privateKey

    catcher :: SqlError -> ConstraintViolation -> IO PublicKey
    catcher _ (UniqueViolation "wallet_pub_key_key") = pure publicKey
    catcher e _                                      = throwIO e

app :: Pool Connection -> FilePath -> Application
app conn staticPath =
  cors (const $ Just policy) $ serve (Proxy @API) (handlers conn staticPath)
  where
    policy =
      simpleCorsResourcePolicy

initializeApplication :: Pool Connection -> FilePath -> IO Application
initializeApplication conn staticPath = pure $ app conn staticPath

testEndpoint :: Handler RawHtml
testEndpoint = return $ RawHtml $ BSL.fromStrict "<html><head><title>Test page</title></head><body><h1>It works!</h1></body></html>"
