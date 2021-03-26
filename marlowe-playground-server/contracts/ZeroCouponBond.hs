{-# LANGUAGE OverloadedStrings #-}
module ZeroCouponBond where

import           Language.Marlowe.Extended

main :: IO ()
main = print . pretty $ contract

discountedPrice, notional :: Value
discountedPrice = ConstantParam "Discounted price"
notional = ConstantParam "Notional"

investor, issuer :: Party
investor = Role "Investor"
issuer = Role "Issuer"

initialExchange, maturityExchangeTimeout :: Timeout
initialExchange = SlotParam "Initial exchange deadline"
maturityExchangeTimeout = SlotParam "Maturity exchange deadline"

transfer :: Timeout -> Party -> Party -> Value -> Contract -> Contract
transfer timeout from to amount continuation =
    When [ Case (Deposit from from ada amount)
                (Pay from (Party to) ada amount continuation) ]
         timeout
         Close

contract :: Contract
contract = transfer initialExchange investor issuer discountedPrice
         $ transfer maturityExchangeTimeout issuer investor notional
           Close
