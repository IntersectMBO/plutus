module CouponBondGuaranteed where

import           Data.List (genericLength)
import           Marlowe

{-# ANN module "HLint: ignore" #-}

main :: IO ()
main = putStrLn $ prettyPrint contract

-------------------------------------
-- Write your code below this line --
-------------------------------------

-- Escrow example using embedding

contract :: Contract
contract = couponBondGuaranteed 1 2 3 1000 0.08 50 100 450 30240

couponBondGuaranteed :: Integer -> Integer -> Integer -> Integer -> Double
                     -> Timeout -> Timeout -> Timeout -> Timeout -> Contract
couponBondGuaranteed creatorID counterpartyID guarantor notionalPrincipal
                     nominalInterestRate initialExchangeDate slotCycle
                     maturityDate gracePeriod =
    -- counterpartyID commits a bond face value before initialExchangeDate
    Commit 1 0 counterpartyID (Constant notionalPrincipal) initialExchangeDate maturityDate
        -- guarantor commits a 'guarantee' before initialExchangeDate
        (Commit 2 1 guarantor (Constant totalPayment) initialExchangeDate (maturityDate + gracePeriod)
            (Both
                -- creatorID can receive the payment from counterpartyID
                (Pay 4 1 creatorID (Committed 0) maturityDate Null Null)
                -- schedule payments
                (Both payments finalPayment)
            )
            -- if no guarantee committed we abort contract and allow to redeem the counterpartyID's commit
            (Pay 3 0 counterpartyID (Committed 0) maturityDate Null Null)
        )
        Null
  where
    cycles = takeWhile (\i ->
            let paymentDate = initialExchangeDate + i * slotCycle
            in paymentDate < maturityDate
        ) [1..]

    -- calculate payment schedule
    paymentDates = map (\i -> initialExchangeDate + i * slotCycle) cycles

    coupon = round $ fromIntegral notionalPrincipal * nominalInterestRate

    -- calculate total amount of payments to be ensured by guarantor
    totalPayment = notionalPrincipal + coupon * genericLength cycles

    -- generate Commit/Pay for each scheduled payment
    payment amount (ident, paymentDate) =
        -- creatorID commits a coupon payment
        Commit baseActionId ident creatorID (Constant amount) paymentDate (maturityDate + gracePeriod)
            (When FalseObs paymentDate Null
                -- counterpartyID can claim the coupon after payment date
                (Pay (baseActionId + 1) ident counterpartyID (Committed ident) (maturityDate + gracePeriod) Null Null))
            -- in case creatorID did not commit on time the guarantor pays the coupon
            (Pay (baseActionId + 2) (ident + 1) counterpartyID (Constant amount) (maturityDate + gracePeriod) Null Null)
        where baseActionId = (5 + ((ident `div` 2) - 1) * 3)

    -- generate coupon payments for given schedule
    payments = foldr1 Both $ map (payment coupon) idsAndDates
        -- generate IdentCC/IdentPay identifiers for each payment date
        where idsAndDates = zip (map (2*) [1..]) paymentDates

    finalPayment = payment notionalPrincipal (2 * (1 + genericLength paymentDates), maturityDate)

