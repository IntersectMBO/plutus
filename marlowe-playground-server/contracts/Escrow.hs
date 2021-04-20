{-# LANGUAGE OverloadedStrings #-}
module Escrow where

import           Language.Marlowe.Extended

main :: IO ()
main = print . pretty $ contract

-- We can set explicitRefunds True to run Close refund analysis
-- but we get a shorter contract if we set it to False
explicitRefunds :: Bool
explicitRefunds = False

seller, buyer, arbiter :: Party
buyer = Role "Buyer"
seller = Role "Seller"
arbiter = Role "Arbiter"

price :: Value
price = ConstantParam "Price"

depositTimeout, disputeTimeout, answerTimeout, arbitrageTimeout :: Timeout
depositTimeout = SlotParam "Buyer's deposit timeout"
disputeTimeout = SlotParam "Buyer's dispute timeout"
answerTimeout = SlotParam "Seller's response timeout"
arbitrageTimeout = SlotParam "Timeout for arbitrage"

choice :: ChoiceName -> Party -> Integer -> Contract -> Case
choice choiceName chooser choiceValue = Case (Choice (ChoiceId choiceName chooser)
                                                     [Bound choiceValue choiceValue])

deposit :: Timeout -> Contract -> Contract -> Contract
deposit timeout timeoutContinuation continuation =
    When [Case (Deposit seller buyer ada price) continuation]
         timeout
         timeoutContinuation

choices :: Timeout -> Party -> Contract -> [(Integer, ChoiceName, Contract)] -> Contract
choices timeout chooser timeoutContinuation list =
    When [choice choiceName chooser choiceValue continuation
          | (choiceValue, choiceName, continuation) <- list]
         timeout
         timeoutContinuation

sellerToBuyer, paySeller :: Contract -> Contract
sellerToBuyer = Pay seller (Account buyer) ada price
paySeller = Pay buyer (Party seller) ada price

refundBuyer :: Contract
refundBuyer
 | explicitRefunds = Pay buyer (Party buyer) ada price Close
 | otherwise = Close

refundSeller :: Contract
refundSeller
 | explicitRefunds = Pay seller (Party seller) ada price Close
 | otherwise = Close

contract :: Contract
contract = deposit depositTimeout Close $
           choices disputeTimeout buyer refundSeller
              [ (0, "Everything is alright"
                , refundSeller
                )
              , (1, "Report problem"
                , sellerToBuyer $
                  choices answerTimeout seller refundBuyer
                     [ (1, "Confirm problem"
                       , refundBuyer
                       )
                     , (0, "Dispute problem"
                       , choices arbitrageTimeout arbiter refundBuyer
                            [ (0, "Dismiss claim"
                              , paySeller
                                Close
                              )
                            , (1, "Confirm problem"
                              , refundBuyer
                              )
                            ]
                       )
                     ]
                )
              ]
