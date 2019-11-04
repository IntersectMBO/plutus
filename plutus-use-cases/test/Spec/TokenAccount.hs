{-# LANGUAGE OverloadedStrings #-}
module Spec.TokenAccount(tests) where

import           Test.Tasty

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Test
import           Language.PlutusTx.Lattice
import qualified Ledger.Ada                                            as Ada
import           Ledger.Value                                          (TokenName, Value)
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

tokenName :: TokenName
tokenName = "test token"

initialiseAccount :: Contract BlockchainActions ContractError Accounts.AccountOwner
initialiseAccount = do
    owner <- Accounts.newAccount tokenName (walletPubKey w1)
    _ <- Accounts.pay owner (Ada.lovelaceValueOf 10)
    pure owner

transferToken :: Accounts.AccountOwner -> Contract BlockchainActions ContractError ()
transferToken owner = pure ()
    
    
theToken :: Value
theToken = Value.singleton "76fcf6ead0de688c0dd68a58ee7a73f0536fc1eeb8cdb1bdda36ef734f94865e" tokenName 1
