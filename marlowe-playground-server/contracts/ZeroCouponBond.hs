{-# LANGUAGE OverloadedStrings #-}
module ZeroCouponBond where

import           Language.Marlowe

main :: IO ()
main = print . pretty $ contract

contract :: Contract
contract = When [ Case
        (Deposit "investor" "investor" (Constant 850))
        (Pay "investor" (Party "issuer") (Constant 850)
            (When
                [ Case (Deposit "investor" "issuer" (Constant 1000))
                        (Pay "investor" (Party "investor" ) (Constant 1000) Refund)
                ]
                (Slot 20)
                Refund
            )
        )
    ]
    (Slot 10)
    Refund
