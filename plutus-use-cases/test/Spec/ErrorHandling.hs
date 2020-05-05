{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}
module Spec.ErrorHandling(tests) where

import           Language.Plutus.Contract.Test

import           Language.PlutusTx.Coordination.Contracts.ErrorHandling

import           Test.Tasty

tests :: TestTree
tests = testGroup "error handling"
    [ checkPredicate @Schema @MyError "throw an error"
        contract
        (assertContractError w1 (\case { TContractError (Error1 _) -> True; _ -> False}) "should throw error")
        (callEndpoint @"throwError" w1 ())

    , checkPredicate @Schema @MyError "catch an error"
        contract
        (assertDone w1 (const True) "should be done")
        (callEndpoint @"catchError" w1 ())

    ]

w1 :: Wallet
w1 = Wallet 1
