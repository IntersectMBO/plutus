{-# LANGUAGE OverloadedStrings #-}
module CouponBondGuaranteed where

import           Language.Marlowe.Extended

main :: IO ()
main = print . pretty $ contract

-- We can set explicitRefunds True to run Close refund analysis
-- but we get a shorter contract if we set it to False
explicitRefunds :: Bool
explicitRefunds = False

guarantor, investor, issuer :: Party
guarantor = Role "Guarantor"
investor = Role "Investor"
issuer = Role "Issuer"

principal, instalment :: Value
principal = ConstantParam "Principal"
instalment = ConstantParam "Interest instalment"

guaranteedAmount :: Integer -> Value
guaranteedAmount instalments = AddValue (MulValue (Constant instalments) instalment) principal

lastInstalment :: Value
lastInstalment = AddValue instalment principal

deposit :: Value -> Party -> Party -> Timeout -> Contract -> Contract -> Contract
deposit amount by toAccount timeout timeoutContinuation continuation =
    When [Case (Deposit toAccount by ada amount) continuation]
         timeout
         timeoutContinuation

refundGuarantor :: Value -> Contract -> Contract
refundGuarantor = Pay investor (Party guarantor) ada

transfer :: Value -> Party -> Party -> Timeout -> Contract -> Contract -> Contract
transfer amount from to timeout timeoutContinuation continuation =
    deposit amount from to timeout timeoutContinuation
  $ Pay to (Party to) ada amount
    continuation

giveCollateralToInvestor :: Value -> Contract
giveCollateralToInvestor amount
  | explicitRefunds = Pay investor (Party investor) ada amount Close
  | otherwise = Close

contract :: Contract
contract = deposit (guaranteedAmount 3) guarantor investor
                   300 Close
         $ transfer principal investor issuer
                    600 (refundGuarantor (guaranteedAmount 3) Close)
         $ transfer instalment issuer investor
                    900 (giveCollateralToInvestor $ guaranteedAmount 3)
         $ refundGuarantor instalment
         $ transfer instalment issuer investor
                    1200 (giveCollateralToInvestor $ guaranteedAmount 2)
         $ refundGuarantor instalment
         $ transfer lastInstalment issuer investor
                    1500 (giveCollateralToInvestor $ guaranteedAmount 1)
         $ refundGuarantor lastInstalment
           Close
