module ZeroCouponBond where

import           Marlowe

{-# ANN module "HLint: ignore" #-}

main :: IO ()
main = putStrLn $ prettyPrint contract

-------------------------------------
-- Write your code below this line --
-------------------------------------

-- Escrow example using embedding

contract :: Contract
contract = zeroCouponBond 1 2 1000 200 10 20 30

zeroCouponBond :: Person -> Person -> Integer -> Integer -> Timeout -> Timeout -> Timeout -> Contract
zeroCouponBond creatorID counterpartyID notionalPrincipal premiumDiscount initialExchangeDate maturityDate gracePeriod =
    -- prepare money for zero-coupon bond, before it could be used
    Commit 1 1 counterpartyID (Constant (notionalPrincipal - premiumDiscount)) initialExchangeDate maturityDate
        -- issuer must commit a full notional value of a bond
        (Commit 2 2 creatorID (Constant notionalPrincipal) initialExchangeDate (maturityDate + gracePeriod)
            (When FalseObs initialExchangeDate Null
                -- after start date but before maturity date the issuer can receive the bond payment
                (Pay 3 1 creatorID (Committed 1) maturityDate
                    (When FalseObs maturityDate Null
                        -- after maturity date the investor can claim bond's full value
                        (Pay 4 2 counterpartyID (Committed 2)
                            (maturityDate + gracePeriod) Null Null)
                    )
                    Null
                )
            )
            Null
        )
        Null

