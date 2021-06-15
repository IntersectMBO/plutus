{-# LANGUAGE OverloadedStrings #-}
module Spec.Uniswap(
    tests
    ) where

import           Plutus.Contract.Test
import qualified Plutus.Contracts.Uniswap.Trace as Uniswap
import           Test.Tasty

tests :: TestTree
tests = testGroup "uniswap" [
    checkPredicate "can create a liquidity pool and add liquidity"
        assertNoFailedTransactions
        Uniswap.uniswapTrace
    ]
