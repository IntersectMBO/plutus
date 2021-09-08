{-# LANGUAGE OverloadedStrings #-}
module ZeroCouponBond where

import           Language.Marlowe.Extended

main :: IO ()
main = print . pretty $ contract

discountedPrice, notionalPrice :: Value
discountedPrice = ConstantParam "Amount"
notionalPrice = AddValue (ConstantParam "Interest") discountedPrice

lender, borrower :: Party
lender = Role "Lender"
borrower = Role "Borrower"

initialExchange, maturityExchangeTimeout :: Timeout
initialExchange = SlotParam "Loan deadline"
maturityExchangeTimeout = SlotParam "Payback deadline"

transfer :: Timeout -> Party -> Party -> Value -> Contract -> Contract
transfer timeout from to amount continuation =
    When [ Case (Deposit from from ada amount)
                (Pay from (Party to) ada amount continuation) ]
         timeout
         Close

contract :: Contract
contract = transfer initialExchange lender borrower discountedPrice
         $ transfer maturityExchangeTimeout borrower lender notionalPrice
           Close
