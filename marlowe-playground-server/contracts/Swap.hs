{-# LANGUAGE OverloadedStrings #-}
module Swap where

import           Language.Marlowe.Extended

main :: IO ()
main = print . pretty $ contract

-- We can set explicitRefunds True to run Close refund analysis
-- but we get a shorter contract if we set it to False
explicitRefunds :: Bool
explicitRefunds = False

lovelacePerAda, amountOfAda, amountOfLovelace, amountOfDollars :: Value
lovelacePerAda = Constant 1000000
amountOfAda = ConstantParam "Amount of Ada"
amountOfLovelace = MulValue lovelacePerAda amountOfAda
amountOfDollars = ConstantParam "Amount of dollars"

adaDepositTimeout, dollarDepositTimeout :: Timeout
adaDepositTimeout = SlotParam "Timeout for Ada deposit"
dollarDepositTimeout = SlotParam "Timeout for dollar deposit"

dollars :: Token
dollars = Token "85bb65" "dollar"

data SwapParty = SwapParty { party    :: Party
                           , currency :: Token
                           , amount   :: Value
                           }

adaProvider, dollarProvider :: SwapParty
adaProvider = SwapParty { party = Role "Ada provider"
                        , currency = ada
                        , amount = amountOfLovelace
                        }
dollarProvider = SwapParty { party = Role "Dollar provider"
                           , currency = dollars
                           , amount = amountOfDollars
                           }

makeDeposit :: SwapParty -> Timeout -> Contract -> Contract -> Contract
makeDeposit src timeout timeoutContinuation continuation =
  When [ Case (Deposit (party src) (party src) (currency src) (amount src))
              continuation
       ] timeout
         timeoutContinuation

refundSwapParty :: SwapParty -> Contract
refundSwapParty swapParty
  | explicitRefunds = Pay (party swapParty) (Party (party swapParty)) (currency swapParty) (amount swapParty) Close
  | otherwise = Close

makePayment :: SwapParty -> SwapParty -> Contract -> Contract
makePayment src dest =
  Pay (party src) (Party $ party dest) (currency src) (amount src)

contract :: Contract
contract = makeDeposit adaProvider adaDepositTimeout Close
         $ makeDeposit dollarProvider dollarDepositTimeout (refundSwapParty adaProvider)
         $ makePayment adaProvider dollarProvider
         $ makePayment dollarProvider adaProvider
           Close
