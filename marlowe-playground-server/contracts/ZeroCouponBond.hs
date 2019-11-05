{-# LANGUAGE OverloadedStrings #-}
module ZeroCouponBond where

import           Language.Marlowe

main :: IO ()
main = print . pretty $ contract

contract :: Contract
contract = When [ Case
        (Deposit "investor" "investor" adaSymbol adaToken (Constant 850))
        (Pay "investor" (Party "issuer") adaSymbol adaToken (Constant 850)
            (When
                [ Case (Deposit "investor" "issuer" adaSymbol adaToken (Constant 1000))
                        (Pay "investor" (Party "investor") adaSymbol adaToken (Constant 1000) Close)
                ]
                (Slot 20)
                Close
            )
        )
    ]
    (Slot 10)
    Close
