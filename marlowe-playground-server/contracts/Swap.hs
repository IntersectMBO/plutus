{-# LANGUAGE OverloadedStrings #-}
module Swap where

import           Language.Marlowe

main :: IO ()
main = print . pretty $ contract

{- Simply swap two payments between parties -}
contract :: Contract
contract =
    When [ Case (Deposit "party1" "party1" ada (Constant 500))
            -- when 1st party committed, wait for 2nd
            (When [ Case (Deposit "party2" "party2" ada (Constant 300))
                (Pay "party1" (Party "party2") ada (Constant 500)
                (Pay "party2" (Party "party1") ada (Constant 300) Close))
                ] date1
            -- if a party dosn't commit, simply Close to the owner
            Close)
        ] (date1 - gracePeriod) Close
  where
    gracePeriod = Slot 5
    date1 = Slot 20
