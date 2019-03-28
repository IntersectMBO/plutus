module ZeroCouponBond where

import           Marlowe

{-# ANN module "HLint: ignore" #-}

main :: IO ()
main = putStrLn $ show contract

-------------------------------------
-- Write your code below this line --
-------------------------------------

-- Escrow example using embedding

contract :: Contract
contract = zeroCouponBond 1 2 1000 200 10 20 30

zeroCouponBond :: Person -> Person -> Integer -> Integer -> Timeout -> Timeout -> Timeout -> Contract
zeroCouponBond issuer investor notional discount startDate maturityDate gracePeriod =
    -- prepare money for zero-coupon bond, before it could be used
    Commit 1 1 investor (Constant (notional - discount)) startDate maturityDate
        -- issuer must commit a full notional value of a bond
        (Commit 2 2 issuer (Constant notional) startDate (maturityDate + gracePeriod)
            (When FalseObs startDate Null
                -- after start date but before maturity date the issuer can receive the bond payment
                (Pay 3 1 issuer (Committed 1) maturityDate
                    (When FalseObs maturityDate Null
                        -- after maturity date the investor can claim bond's full value
                        (Pay 4 2 investor (Committed 2)
                            (maturityDate + gracePeriod) Null Null)
                    )
                    Null
                )
            )
            Null
        )
        Null
