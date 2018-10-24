{-# LANGUAGE DataKinds #-}

module Wallet.Emulator.Client where

import           Data.Proxy            (Proxy (Proxy))
import           Data.Set              (Set)
import           Servant.API           ((:<|>) ((:<|>)), NoContent)
import           Servant.Client        (ClientM, client)
import           Wallet.Emulator.Http  (API)
import           Wallet.Emulator.Types (Wallet)
import           Wallet.UTXO           (Block, Height, Tx, TxIn', TxOut', ValidationData, Value)

api :: Proxy API
api = Proxy

wallets :: ClientM [Wallet]
fetchWallet :: Wallet -> ClientM Wallet
createWallet :: Wallet -> ClientM NoContent
createPaymentWithChange :: Wallet -> Value -> ClientM (Set TxIn', TxOut')
payToPublicKey :: Wallet -> Value -> ClientM TxOut'
submitTxn :: Wallet -> Tx -> ClientM ()
getTransactions :: ClientM [Tx]
blockchainActions :: ClientM [Tx]
setValidationData :: ValidationData -> ClientM ()
blockValidated :: Wallet -> Block -> ClientM ()
blockHeight :: Wallet -> Height -> ClientM ()
assertOwnFundsEq :: Wallet -> Value -> ClientM NoContent
assertIsValidated :: Tx -> ClientM NoContent
(wallets :<|> fetchWallet :<|> createWallet :<|> createPaymentWithChange :<|> payToPublicKey :<|> submitTxn :<|> getTransactions) :<|> (blockValidated :<|> blockHeight) :<|> (blockchainActions :<|> setValidationData) :<|> (assertOwnFundsEq :<|> assertIsValidated) =
  client api
