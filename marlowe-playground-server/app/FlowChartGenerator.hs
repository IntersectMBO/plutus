{-# LANGUAGE OverloadedStrings #-}

module Main
    ( main,
    )
    where

import qualified ContractForDifferences           as ContractForDifferences
import qualified ContractForDifferencesWithOracle as ContractForDifferencesWithOracle
import qualified CouponBondGuaranteed             as CouponBondGuaranteed
import qualified Escrow                           as Escrow
import qualified EscrowWithCollateral             as EscrowWithCollateral
import           Marlowe.Mermaid                  (toMermaid)
import qualified Swap                             as Swap
import qualified ZeroCouponBond                   as ZeroCouponBond

main :: IO ()
main = do
    putStrLn "===== SIMPLE ESCROW ====="
    putStrLn $ toMermaid Escrow.contract
    putStrLn "===== ESCROW WITH COLLATERAL ====="
    putStrLn $ toMermaid EscrowWithCollateral.contract
    putStrLn "===== ZERO COUPON BOND ====="
    putStrLn $ toMermaid ZeroCouponBond.contract
    putStrLn "===== COUPON BOND GUARANTEED ====="
    putStrLn $ toMermaid CouponBondGuaranteed.contract
    putStrLn "===== SWAP OF ADA AND DOLLAR TOKENS ====="
    putStrLn $ toMermaid Swap.contract
    putStrLn "===== CONTRACT FOR DIFFERENCES ====="
    putStrLn $ toMermaid ContractForDifferences.contract
    putStrLn "===== CONTRACT FOR DIFFERENCES WITH ORACLE ====="
    putStrLn $ toMermaid ContractForDifferencesWithOracle.contract
