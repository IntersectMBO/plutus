{-# LANGUAGE OverloadedStrings #-}
module Spec.TokenAccount(tests) where

import           Test.Tasty

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Test
import           Language.PlutusTx.Lattice
import qualified Ledger.Ada                                            as Ada
import           Ledger.Value                                          (Value)
import qualified Ledger.Value                                          as Value

import qualified Language.PlutusTx.Coordination.Contracts.TokenAccount as Accounts

tests :: TestTree
tests = testGroup "token account"
    [ checkPredicate "Create a token account"
        initialiseAccount
        (assertNoFailedTransactions
        /\ assertDone w1 (const True) "wallet 1 should be done"
        /\ walletFundsChange w1 (Ada.lovelaceValueOf (-10) <> theToken))
        (handleBlockchainEvents w1)

    , checkPredicate "Redeem all funds"
        (initialiseAccount >>= Accounts.redeem (walletPubKey w1))
        (assertNoFailedTransactions
        /\ assertDone w1 (const True) "wallet 1 should be done"
        /\ walletFundsChange w1 theToken)
        (handleBlockchainEvents w1)

    ]

w1 :: Wallet
w1 = Wallet 1

initialiseAccount :: Contract BlockchainActions ContractError Accounts.AccountOwner
initialiseAccount = do
    owner <- Accounts.newAccount (walletPubKey w1)
    _ <- Accounts.pay owner (Ada.lovelaceValueOf 10)
    pure owner

transferToken :: Accounts.AccountOwner -> Contract BlockchainActions ContractError ()
transferToken owner = do

theToken :: Value
theToken = Value.singleton "a0b191313cb85a707853d6729023b77838a703fc3a70629d28bb7e8cd8633fea" "token-account" 1
