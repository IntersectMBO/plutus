{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Server where

import           API                               (API, CreateContractRequest (..), JSON_API, PLAIN_API, PrivateKey,
                                                    PublicKey, RawHtml (..), TransferRequest (..))
import           Control.Concurrent                (threadDelay)
import           Control.Exception                 (throwIO)
import           Control.Monad.Except              (ExceptT, void)
import           Control.Monad.IO.Class            (MonadIO, liftIO)
import           Control.Monad.Logger              (LoggingT, MonadLogger, logInfoN, runStderrLoggingT)
import           Control.Monad.Reader              (ReaderT, runReaderT)
import qualified Crypto.Hash.SHA256                as SHA256
import           Data.Aeson                        (FromJSON, ToJSON, eitherDecode, encode)
import qualified Data.Aeson                        as Aeson
import qualified Data.ByteString                   as BS
import qualified Data.ByteString.Base16            as B16
import qualified Data.ByteString.Lazy              as BSL
import qualified Data.ByteString.Lazy.UTF8         as BSLU
import qualified Data.ByteString.UTF8              as BSU
import           Data.Either                       (fromRight)
import           Data.Map                          (Map)
import qualified Data.Map                          as Map
import           Data.Pool                         (Pool, withResource)
import           Data.Proxy                        (Proxy (Proxy))
import           Data.Ratio                        (Ratio, denominator, numerator)
import           Data.Set                          (Set)
import qualified Data.Set                          as Set
import           Data.String                       as S
import           Data.Text                         (Text)
import qualified Data.Text                         as Text
import qualified Data.Text.Encoding                as TE
import           Data.Time.Clock                   (diffUTCTime, getCurrentTime, nominalDiffTimeToSeconds)
import           Database.PostgreSQL.Simple        (Connection, FromRow, Only (..), SqlError, execute, executeMany,
                                                    query, query_, returning)
import           Database.PostgreSQL.Simple.Errors (ConstraintViolation (..), catchViolation)
import           Database.PostgreSQL.Simple.SqlQQ  (sql)
import           GHC.Generics                      (Generic)
import           Language.Marlowe                  (Contract (Close), Slot (Slot), emptyState, extractContractRoles)
import           Network.Wai.Middleware.Cors       (cors, corsRequestHeaders, simpleCorsResourcePolicy)
import           Plutus.V1.Ledger.Value            (CurrencySymbol (..), TokenName (..))
import           Servant                           (Application, Handler (Handler), Server, ServerError, hoistServer,
                                                    serve, serveDirectoryFileServer, throwError, (:<|>) ((:<|>)), (:>))

fromCurrencySymbol :: CurrencySymbol -> String
fromCurrencySymbol =  Text.unpack . TE.decodeUtf8 . B16.encode . unCurrencySymbol

toCurrencySymbol :: String -> CurrencySymbol
toCurrencySymbol = CurrencySymbol . fromRight mempty . B16.decode . TE.encodeUtf8 . Text.pack

handlersJSON :: Pool Connection -> FilePath -> Server JSON_API
handlersJSON conns staticPath = createWallet conns :<|>
                                listWalletFunds conns :<|>
                                transferFundsJSON conns :<|>
                                createContractJSON conns

handlersPlain :: Pool Connection -> FilePath -> Server PLAIN_API
handlersPlain conns staticPath = showResult . createWallet conns :<|>
                                 showResult . listWalletFunds conns :<|>
                                 transferFundsPlain conns :<|>
                                 createContractPlain conns

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
      pure $ Map.fromListWith (++) [(toCurrencySymbol cs, [(TokenName tn, fromRatio am)]) | (cs, tn, am) <- result]



-- Creates a transaction to transfer funds
transferFunds :: Pool Connection -> PrivateKey -> CurrencySymbol -> TokenName -> Integer -> PublicKey -> Handler ()
transferFunds conns srcPrivKey currSym (TokenName tok) amount destPubKey =
  let curr = fromCurrencySymbol currSym in
  liftIO . withResource conns $ \conn -> do
    if amount > 0 then do
      execute conn
        [sql|WITH source_container AS (SELECT get_or_create_money_container_id_from_pubkey(?) AS id),
                  destination_container AS (SELECT get_or_create_money_container_id_from_pubkey(?) AS id),
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
    else pure ()
  where
    srcPubKey = BSU.toString $ B16.encode $ SHA256.hash $ BSU.fromString srcPrivKey

transferFundsPlain :: Pool Connection -> String -> String -> String -> Integer -> String -> Handler String
transferFundsPlain conns srcPrivKey curr tok amount destPubKey =
  show <$> transferFunds conns srcPrivKey (toCurrencySymbol curr) (TokenName (BSU.fromString tok)) amount destPubKey

transferFundsJSON :: Pool Connection -> API.TransferRequest -> Handler ()
transferFundsJSON conns TransferRequest{ src_priv_key = src_priv_key
                                       , currency_symbol = currency_symbol
                                       , token_symbol = token_symbol
                                       , amount = amount
                                       , dest_pub_key = dest_pub_key
                                       } = transferFunds conns src_priv_key currency_symbol token_symbol amount dest_pub_key

createContractPlain :: Pool Connection -> String -> String -> String -> Handler String
createContractPlain conns creator_priv_key role_distribution contract =
  show <$> createContract conns (read creator_priv_key) ([(TokenName name, pubkey) | (name, pubkey) <- read role_distribution]) (fromRight Close $ eitherDecode $ BSLU.fromString contract)

createContractJSON :: Pool Connection -> API.CreateContractRequest -> Handler (Either String CurrencySymbol)
createContractJSON conns CreateContractRequest { creator_priv_key = creator_priv_key
                                               , role_distribution = role_distribution
                                               , contract = contract
                                               } =
  createContract conns creator_priv_key role_distribution contract

createContract :: Pool Connection -> PrivateKey -> [(TokenName, PublicKey)] -> Contract -> Handler (Either String CurrencySymbol)
createContract conns privkey distrib contract =
  let owners = Map.fromList distrib :: Map TokenName PublicKey
      ownerTokenNames = Map.keys owners
      ownerTokenNamesStr = map unTokenName ownerTokenNames
      roles = extractContractRoles contract in
  if roles `Set.isSubsetOf` Set.fromList (Map.keys owners)
  then
    liftIO . withResource conns $ \conn -> do
      [Only currencySymbol] <- query_ conn [sql| WITH curr_sym AS (INSERT INTO currency_symbol (currency_symbol)
                                                                   VALUES ((SELECT encode(digest(COUNT(currency_symbol)::text,'sha256'),'hex') FROM currency_symbol))
                                                                   RETURNING currency_symbol)
                                                 SELECT cs.currency_symbol FROM curr_sym cs
                                           |] :: IO [Only String]
      executeMany conn [sql| INSERT INTO token (currency_symbol, token_name)
                             VALUES (?, ?)
                       |] ([(currencySymbol, BSU.toString tns) | tns <- ownerTokenNamesStr] :: [(String, String)])
      sequence_ [execute conn [sql| INSERT INTO currency_amount (amount, currency_symbol, token_name, money_container_id)
                                    VALUES (?, ?, ?, get_or_create_money_container_id_from_pubkey(?))
                              |] (1 :: Integer, currencySymbol, BSU.toString tns, pk) | (TokenName tns, pk) <- Map.toList owners ]
      [Only currSlot] <- query_ conn
                      [sql| SELECT MAX(slot_number) + 1
                            FROM slot
                      |]
      [Only moneyContainerId] <- query_ conn
                              [sql| INSERT INTO money_container DEFAULT VALUES
                                    RETURNING money_container_id AS id |]
      let contractJSON = Aeson.encode contract
          stateJSON = Aeson.encode $ emptyState (Slot $ fromRatio currSlot)
      execute conn [sql| INSERT INTO contract (money_container_id, contract, state, currency_symbol, original_contract, original_state)
                         VALUES (?, ?, ?, ?, ?, ?)
                   |] (fromRatio moneyContainerId, contractJSON, stateJSON, currencySymbol, contractJSON, stateJSON)
      pure $ Right (toCurrencySymbol currencySymbol)
  else let missingRoles = roles `Set.difference` Set.fromList ownerTokenNames in
       pure $ Left $ "You didn't specify owners of these roles: " <> show missingRoles

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
     -- Process transactions
     transactionIds <- query conn
                          [sql| WITH chosen_transactions AS (SELECT transaction_id
                                                             FROM transaction
                                                             WHERE slot_number IS NULL
                                                             LIMIT 30)
                                UPDATE transaction ut
                                SET slot_number = ?
                                FROM chosen_transactions st
                                WHERE st.transaction_id = ut.transaction_id
                                RETURNING st.transaction_id; |] [fromRatio result]
     sequence_ [ void (query conn [sql| SELECT process_transaction(?); |] [fromRatio transactionId] :: (IO [Only Bool])) | Only transactionId <- transactionIds]
     -- Validate slot
     execute conn
        [sql| UPDATE slot SET is_settled = true WHERE slot_number = ? |] [fromRatio result]

     after <- getCurrentTime
     threadDelay $ max 0 (round (1000000 - nominalDiffTimeToSeconds (diffUTCTime after before) * 1000000))
     miner conn

