{-# LANGUAGE OverloadedStrings #-}
module CouponBondGuaranteed where

import           Language.Marlowe.Extended

main :: IO ()
main = print . pretty $ contract

contract :: Contract
contract = When [Case (Deposit "investor" "guarantor" ada (Constant 1030))
    (When [Case (Deposit "investor" "investor" ada (Constant 1000))
        (Pay "investor" (Party "issuer") ada (Constant 1000)
            (When [Case (Deposit "investor" "issuer" ada (Constant 10))
                (Pay "investor" (Party "investor" ) ada (Constant 10)
                (Pay "investor" (Party "guarantor") ada (Constant 10)
                    (When [Case (Deposit "investor" "issuer" ada (Constant 10))
                        (Pay "investor" (Party "investor" ) ada (Constant 10)
                        (Pay "investor" (Party "guarantor") ada (Constant 10)
                            (When [Case (Deposit "investor" "issuer" ada (Constant 1010))
                                (Pay "investor" (Party "investor" ) ada (Constant 1010)
                                (Pay "investor" (Party "guarantor") ada (Constant 1010) Close))]
                            (Slot 20) Close)))]
                    (Slot 15) Close)))]
            (Slot 10) Close))]
    (Slot 5) Close)]
    (Slot 5) Close

