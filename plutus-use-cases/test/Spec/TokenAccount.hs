{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module Spec.TokenAccount(tests) where

import           Test.Tasty

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Test
import           Language.PlutusTx.Lattice
import qualified Ledger.Ada                                            as Ada
import           Ledger.Value                                          (TokenName, Value)

import qualified Language.PlutusTx.Coordination.Contracts.TokenAccount as Accounts
import Language.PlutusTx.Coordination.Contracts.TokenAccount (AccountOwner(..), TokenAccountSchema, tokenAccountContract)

tests :: TestTree
tests = testGroup "token account"
    [ checkPredicate @TokenAccountSchema @ContractError "Create a token account"
        tokenAccountContract
        (assertNoFailedTransactions
        /\ assertNotDone w1 "contract should not have any errors"
        /\ walletFundsChange w1 theToken)
        (  callEndpoint @"new-account" w1 (tokenName, walletPubKey w1)
        >> handleBlockchainEvents w1)

    , checkPredicate @TokenAccountSchema @ContractError "Pay into the account"
        tokenAccountContract
        (assertNoFailedTransactions
        /\ assertNotDone w1 "contract should not have any errors"
        -- /\ assertDone w1 (const True) ""
        -- /\ emulatorLog (const False) ""
        /\ walletFundsChange w1 (Ada.lovelaceValueOf (-10) <> theToken))
        ( callEndpoint @"new-account" w1 (tokenName, walletPubKey w1)
        >> handleBlockchainEvents w1
        >> addBlocks 1
        >> callEndpoint @"pay" w1 (accountOwner, Ada.lovelaceValueOf 10)
        >> handleBlockchainEvents w1
        >> addBlocks 1)

    -- , checkPredicate @TokenAccountSchema @ContractError "Transfer & redeem all funds"
    --     tokenAccountContract
    --     (assertNoFailedTransactions
    --     /\ assertNotDone w1 "contract should not have any errors"
    --     /\ walletFundsChange w1 (Ada.lovelaceValueOf (-10))
    --     /\ walletFundsChange w2 (theToken <> Ada.lovelaceValueOf 10))
    --     (  callEndpoint @"new-account" w1 (tokenName, walletPubKey w1)
    --     >> handleBlockchainEvents w1
    --     >> callEndpoint @"pay" w1 (accountOwner, Ada.lovelaceValueOf 10)
    --     >> handleBlockchainEvents w1
    --     >> callEndpoint @"transfer-token" w1 (accountOwner, walletPubKey w2)
    --     >> handleBlockchainEvents w1
    --     >> callEndpoint @"redeem" w2 (accountOwner, walletPubKey w2)
    --     >> handleBlockchainEvents w2)

    ]

w1, w2 :: Wallet
w1 = Wallet 1
w2 = Wallet 2

tokenName :: TokenName
tokenName = "test token"

accountOwner :: AccountOwner
accountOwner = 
    let currencySymbol = "76fcf6ead0de688c0dd68a58ee7a73f0536fc1eeb8cdb1bdda36ef734f94865e"
    in AccountOwner (currencySymbol, tokenName)

theToken :: Value
theToken = Accounts.accountToken accountOwner
