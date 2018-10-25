{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Wallet.Emulator.Client where

import           Control.Monad.Reader  (ReaderT, asks, lift, runReaderT)
import           Data.Proxy            (Proxy (Proxy))
import           Data.Set              (Set)
import           Servant.API           ((:<|>) ((:<|>)), NoContent)
import           Servant.Client        (ClientEnv, ClientM, ServantError, client, runClientM)
import           Wallet.API            (KeyPair, WalletAPI (..))
import           Wallet.Emulator.Http  (API)
import           Wallet.Emulator.Types (Wallet)
import           Wallet.UTXO           (Block, Height, Tx, TxIn', TxOut', ValidationData, Value)

api :: Proxy API
api = Proxy

wallets' :: ClientM [Wallet]
fetchWallet' :: Wallet -> ClientM Wallet
createWallet' :: Wallet -> ClientM NoContent
createPaymentWithChange' :: Wallet -> Value -> ClientM (Set TxIn', TxOut')
payToPublicKey' :: Wallet -> Value -> ClientM TxOut'
submitTxn' :: Wallet -> Tx -> ClientM ()
getTransactions' :: ClientM [Tx]
blockchainActions' :: ClientM [Tx]
setValidationData' :: ValidationData -> ClientM ()
blockValidated' :: Wallet -> Block -> ClientM ()
blockHeight' :: Wallet -> Height -> ClientM ()
assertOwnFundsEq' :: Wallet -> Value -> ClientM NoContent
assertIsValidated' :: Tx -> ClientM NoContent
(wallets' :<|> fetchWallet' :<|> createWallet' :<|> createPaymentWithChange' :<|> payToPublicKey' :<|> submitTxn' :<|> getTransactions') :<|> (blockValidated' :<|> blockHeight') :<|> (blockchainActions' :<|> setValidationData') :<|> (assertOwnFundsEq' :<|> assertIsValidated') =
  client api

data Environment = Environment
  { getWallet    :: Wallet
  , getKeyPair   :: KeyPair
  , getClientEnv :: ClientEnv
  }

type WalletClient = ReaderT Environment ClientM

runWalletClient :: Environment -> WalletClient a -> IO (Either ServantError a)
runWalletClient env act = runClientM (runReaderT act env) (getClientEnv env)

liftWallet :: (Wallet -> ClientM a) -> WalletClient a
liftWallet action = do
  wallet <- asks getWallet
  lift $ action wallet

instance WalletAPI WalletClient where
  submitTxn tx = liftWallet (`submitTxn'` tx)
  myKeyPair = asks getKeyPair
  createPaymentWithChange value = liftWallet (`createPaymentWithChange'` value)
  register _ _ = pure () -- TODO: Keep track of triggers in emulated wallet
  payToPublicKey value = liftWallet (`payToPublicKey'` value)
