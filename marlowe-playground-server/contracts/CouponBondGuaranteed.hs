{-# LANGUAGE OverloadedStrings #-}
module CouponBondGuaranteed where

import           Language.Marlowe

main :: IO ()
main = print . pretty $ contract

contract :: Contract
contract = When [Case (Deposit "investor" "guarantor" (Constant 1030))
    (When [Case (Deposit "investor" "investor" (Constant 1000))
        (Pay "investor" (Party "issuer") (Constant 1000)
            (When [Case (Deposit "investor" "issuer" (Constant 10))
                (Pay "investor" (Party "investor" ) (Constant 10)
                (Pay "investor" (Party "guarantor") (Constant 10)
                    (When [Case (Deposit "investor" "issuer" (Constant 10))
                        (Pay "investor" (Party "investor" ) (Constant 10)
                        (Pay "investor" (Party "guarantor") (Constant 10)
                            (When [Case (Deposit "investor" "issuer" (Constant 1010))
                                (Pay "investor" (Party "investor" ) (Constant 1010)
                                (Pay "investor" (Party "guarantor") (Constant 1010) Refund))]
                            (Slot 20) Refund)))]
                    (Slot 15) Refund)))]
            (Slot 10) Refund))]
    (Slot 5) Refund)]
    (Slot 5) Refund
