{-# LANGUAGE OverloadedStrings #-}
module Spec.Uniswap(
    tests
    ) where

import           Plutus.Contract.Test
import qualified Plutus.Contracts.Uniswap.Trace as Uniswap
import qualified Plutus.Trace.Emulator          as Trace

import           Test.Tasty

tests :: TestTree
tests = testGroup "uniswap" [
    checkPredicate "can create a liquidity pool and add liquidity"
        (assertNotDone Uniswap.setupTokens
                       (Trace.walletInstanceTag (Wallet 1))
                       "setupTokens contract should be still running"
        .&&. assertNoFailedTransactions)
        Uniswap.uniswapTrace
    ]
