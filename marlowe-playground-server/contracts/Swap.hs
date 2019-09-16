{-# LANGUAGE OverloadedStrings #-}
module Swap where

import           Language.Marlowe

main :: IO ()
main = print . pretty $ contract

{- Simply swap two payments between parties -}
contract :: Contract
contract =
    When [ Case (Deposit acc1 "party1" (Constant 500))
            -- when 1st party committed, wait for 2nd
            (When [ Case (Deposit acc2 "party2" (Constant 300))
                (Pay acc1 (Party "party2") (Constant 500)
                (Pay acc2 (Party "party1") (Constant 300) Refund))
                ] date1
            -- if a party dosn't commit, simply Refund to the owner
            Refund)
          , Case (Deposit acc2 "party2" (Constant 300))
            -- if 2nd party committed first wait for 1st
            (When [ Case (Deposit acc1 "party1" (Constant 500))
                -- we can just pay a diff between account and refund
                (Pay acc1 (Account acc2) (Constant 200) Refund)
            ] date1
            -- if a party dosn't commit, simply Refund to the owner
            Refund)
        ] (date1 - gracePeriod) Refund
  where
    gracePeriod = Slot 5
    date1 = Slot 20
    acc1 = AccountId 1 "party1"
    acc2 = AccountId 2 "party2"
