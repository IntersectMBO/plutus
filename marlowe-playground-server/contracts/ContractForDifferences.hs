{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}
module ContractForDifferences where

import           Language.Marlowe.Extended

main :: IO ()
main = print . pretty $ contract

-- We can set explicitRefunds True to run Close refund analysis
-- but we get a shorter contract if we set it to False
explicitRefunds :: Bool
explicitRefunds = False

party, counterparty, oracle :: Party
party = Role "Party"
counterparty = Role "Counterparty"
oracle = Role "Oracle"

depositAmount :: Integer
depositAmount = 100_000_000

deposit, doubleDeposit :: Value
deposit = Constant depositAmount
doubleDeposit = Constant (depositAmount * 2)

priceBeginning, priceEnd :: ChoiceId
priceBeginning = ChoiceId "Price at beginning" oracle
priceEnd = ChoiceId "Price at end" oracle

decreaseInPrice, increaseInPrice :: ValueId
decreaseInPrice = "Decrease in price"
increaseInPrice = "Increase in price"

initialDeposit :: Party -> Timeout -> Contract -> Contract -> Contract
initialDeposit by timeout timeoutContinuation continuation =
  When [Case (Deposit by by ada deposit) continuation]
       timeout
       timeoutContinuation

oracleInput :: ChoiceId -> Timeout -> Contract -> Contract -> Contract
oracleInput choiceId timeout timeoutContinuation continuation =
  When [Case (Choice choiceId [Bound 0 1_000_000_000]) continuation]
       timeout
       timeoutContinuation

wait :: Timeout -> Contract -> Contract
wait = When []

gtLtEq :: Value -> Value -> Contract -> Contract -> Contract -> Contract
gtLtEq value1 value2 gtContinuation ltContinuation eqContinuation =
     If (ValueGT value1 value2) gtContinuation
   $ If (ValueLT value1 value2) ltContinuation
                                eqContinuation

recordDifference :: ValueId -> ChoiceId -> ChoiceId -> Contract -> Contract
recordDifference name choiceId1 choiceId2 =
   Let name (SubValue (ChoiceValue choiceId1) (ChoiceValue choiceId2))

transferUpToDeposit :: Party -> Party -> Value -> Contract -> Contract
transferUpToDeposit from to amount =
   Pay from (Account to) ada (Cond (ValueLT amount deposit) amount deposit)

refund :: Party -> Value -> Contract -> Contract
refund who amount
  | explicitRefunds = Pay who (Party who) ada amount
  | otherwise = id

refundBoth :: Contract
refundBoth = refund party deposit (refund counterparty deposit Close)

refundIfGtZero :: Party -> Value -> Contract -> Contract
refundIfGtZero who amount continuation
  | explicitRefunds = If (ValueGT amount (Constant 0)) (refund who amount continuation) continuation
  | otherwise = continuation

refundUpToDoubleOfDeposit :: Party -> Value -> Contract -> Contract
refundUpToDoubleOfDeposit who amount
  | explicitRefunds = refund who $ Cond (ValueGT amount doubleDeposit) doubleDeposit amount
  | otherwise = id

refundAfterDifference :: Party -> Party -> Value -> Contract
refundAfterDifference payer payee difference =
    refundIfGtZero payer (SubValue deposit difference)
  $ refundUpToDoubleOfDeposit payee (AddValue deposit difference)
    Close

contract :: Contract
contract = initialDeposit party 300 Close
         $ initialDeposit counterparty 600 (refund party deposit Close)
         $ oracleInput priceBeginning 900 refundBoth
         $ wait 1500
         $ oracleInput priceEnd 1800 refundBoth
         $ gtLtEq (ChoiceValue priceBeginning) (ChoiceValue priceEnd)
                  ( recordDifference decreaseInPrice priceBeginning priceEnd
                  $ transferUpToDeposit counterparty party (UseValue decreaseInPrice)
                  $ refundAfterDifference counterparty party (UseValue decreaseInPrice)
                  )
                  ( recordDifference increaseInPrice priceEnd priceBeginning
                  $ transferUpToDeposit party counterparty (UseValue increaseInPrice)
                  $ refundAfterDifference party counterparty (UseValue increaseInPrice)
                  )
                  refundBoth
