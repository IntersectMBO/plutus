{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}
module ZeroCouponBond where

import           Language.Marlowe

main :: IO ()
main = print . pretty $ contract

contract :: Contract
contract = When [ Case
        (Deposit "investor" "investor" ada (Constant 850_000))
        (Pay "investor" (Party "issuer") ada (Constant 850_000)
            (When
                [ Case (Deposit "investor" "issuer" ada (Constant 1000_000))
                        (Pay "investor" (Party "investor") ada (Constant 1000_000) Close)
                ]
                (Slot 20)
                Close
            )
        )
    ]
    (Slot 10)
    Close
