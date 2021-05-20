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

import           API                               (API, JSON_API, PLAIN_API, PrivateKey, PublicKey, RawHtml (..),
                                                    TransferRequest (..))
import           Control.Concurrent                (threadDelay)
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
import           Data.Map                          (Map)
import qualified Data.Map                          as Map
import           Data.Pool                         (Pool, withResource)
import           Data.Proxy                        (Proxy (Proxy))
import           Data.Ratio                        (Ratio, denominator, numerator)
import           Data.String                       as S
import           Data.Text                         (Text)
import qualified Data.Text                         as Text
import           Data.Time.Clock                   (diffUTCTime, getCurrentTime, nominalDiffTimeToSeconds)
import           Database.PostgreSQL.Simple        (Connection, Only (..), SqlError, execute, query, query_)
import           Database.PostgreSQL.Simple.Errors (ConstraintViolation (..), catchViolation)
import           Database.PostgreSQL.Simple.SqlQQ  (sql)
import           GHC.Generics                      (Generic)
import           Language.Marlowe                  (Contract)
import           Network.Wai.Middleware.Cors       (cors, corsRequestHeaders, simpleCorsResourcePolicy)
import           Plutus.V1.Ledger.Value            (CurrencySymbol (..), TokenName (..))
import           Servant                           (Application, Handler (Handler), Server, ServerError, hoistServer,
                                                    serve, serveDirectoryFileServer, throwError, (:<|>) ((:<|>)), (:>))

handlersJSON :: Pool Connection -> FilePath -> Server JSON_API
handlersJSON conns staticPath = createWallet conns :<|>
                                listWalletFunds conns :<|>
                                transferFundsJSON conns

handlersPlain :: Pool Connection -> FilePath -> Server PLAIN_API
handlersPlain conns staticPath = showResult . createWallet conns :<|>
                                 showResult . listWalletFunds conns :<|>
                                 transferFundsPlain conns

handlers :: Pool Connection -> FilePath -> Server API
handlers conns staticPath = handlersJSON conns staticPath :<|>
                            handlersPlain conns staticPath :<|>
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

-- Lists the amount a wallet has of each currency (of currencies it ever had some amount of)
listWalletFunds :: Pool Connection -> PublicKey -> Handler (Map CurrencySymbol [(TokenName, Integer)])
listWalletFunds conns publicKey =
  liftIO . withResource conns $ \conn -> do
      result <- query conn
                  [sql| SELECT ca.currency_symbol, ca.token_name, SUM(amount) AS amount
                        FROM wallet w INNER JOIN currency_amount ca
                          ON w.money_container_id = ca.money_container_id
                        WHERE w.pub_key = ?
                        GROUP BY ca.currency_symbol, ca.token_name
                  |] [publicKey]
      pure $ Map.fromListWith (++) [(CurrencySymbol cs, [(TokenName tn, fromRatio am)]) | (cs, tn, am) <- result]



-- Creates a transaction to transfer funds
transferFunds :: Pool Connection -> PrivateKey -> CurrencySymbol -> TokenName -> Integer -> PublicKey -> Handler ()
transferFunds conns srcPrivKey (CurrencySymbol curr) (TokenName tok) amount destPubKey =
  liftIO . withResource conns $ \conn -> do
    catchViolation catcher $ do
      execute conn
        [sql|WITH source_container AS (SELECT money_container_id AS id FROM wallet WHERE pub_key = ?),
                  destination_container AS (SELECT money_container_id AS id FROM wallet WHERE pub_key = ?),
                  main_transaction AS (INSERT INTO transaction (signing_wallet_id)
                                       VALUES ((SELECT id FROM source_container))
                                       RETURNING transaction_id AS id)
              INSERT INTO transaction_line (transaction_id, line_num, money_container_id, amount_change, currency_symbol, token_name)
              VALUES ((SELECT id FROM main_transaction), 1, (SELECT id FROM source_container), ?, ?, ?),
                     ((SELECT id FROM main_transaction), 2, (SELECT id FROM destination_container), ?, ?, ?)|]
                   (srcPubKey,
                    destPubKey,
                    amount, curr, tok, -amount, curr, tok)
      pure ()
  where
    srcPubKey = BSU.toString $ B16.encode $ SHA256.hash $ BSU.fromString srcPrivKey

    catcher :: SqlError -> ConstraintViolation -> IO ()
    catcher e _                                      = throwIO e

transferFundsPlain :: Pool Connection -> String -> String -> String -> Integer -> String -> Handler String
transferFundsPlain conns srcPrivKey curr tok amount destPubKey =
  show <$> transferFunds conns srcPrivKey (CurrencySymbol (BSU.fromString curr)) (TokenName (BSU.fromString tok)) amount destPubKey

transferFundsJSON :: Pool Connection -> API.TransferRequest -> Handler ()
transferFundsJSON = error "not implemented"

fromRatio :: Ratio Integer -> Integer
fromRatio am = numerator am `div` denominator am

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

miner :: Connection -> IO ()
miner conn =
  do before <- getCurrentTime
     -- Create slot placeholder
     [Only result] <- query_ conn
                        [sql| WITH new_slot AS (INSERT INTO slot DEFAULT VALUES
                                                RETURNING slot_number)
                              SELECT slot_number FROM new_slot
                        |]
     -- Validate slot
     execute conn
        [sql| UPDATE slot SET is_settled = true WHERE slot_number = ? |] [result :: Integer]

     after <- getCurrentTime
     threadDelay $ max 0 (round (1000000 - nominalDiffTimeToSeconds (diffUTCTime after before) * 1000000))
     miner conn

