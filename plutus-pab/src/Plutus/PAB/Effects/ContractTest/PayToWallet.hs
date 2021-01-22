{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
module Plutus.PAB.Effects.ContractTest.PayToWallet(
    payToWallet
    , PayToWalletParams(..)
    , PayToWalletSchema
    ) where

import           Data.Aeson               (FromJSON, ToJSON)
import           GHC.Generics             (Generic)
import           IOTS                     (IotsType)
import           Schema                   (ToSchema)

import           Language.Plutus.Contract
import           Ledger                   (Value, txId)
import           Ledger.Constraints
import           Ledger.Crypto            (pubKeyHash)
import           Wallet.Emulator.Types    (Wallet, walletPubKey)

data PayToWalletParams =
    PayToWalletParams
        { amount :: Value
        , wallet :: Wallet
        }
        deriving stock (Eq, Show, Generic)
        deriving anyclass (ToJSON, FromJSON, IotsType, ToSchema)

type PayToWalletSchema =
  BlockchainActions .\/ Endpoint "Pay to wallet" PayToWalletParams

payToWallet :: Contract PayToWalletSchema ContractError ()
payToWallet = do
  PayToWalletParams{amount, wallet} <- endpoint @"Pay to wallet"
  let pkh = pubKeyHash $ walletPubKey wallet
  txid <- submitTx (mustPayToPubKey pkh amount)
  awaitTxConfirmed (txId txid)
