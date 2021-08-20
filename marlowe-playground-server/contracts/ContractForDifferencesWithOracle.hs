{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}
module ContractForDifferencesWithOracle where

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
oracle = Role "kraken"

partyDeposit, counterpartyDeposit, bothDeposits :: Value
partyDeposit = ConstantParam "Amount paid by party"
counterpartyDeposit = ConstantParam "Amount paid by counterparty"
bothDeposits = AddValue partyDeposit counterpartyDeposit

priceBeginning :: Value
priceBeginning = ConstantParam "Amount of Ada to use as asset"

priceEnd :: ValueId
priceEnd = "Price in second window"

exchangeBeginning, exchangeEnd :: ChoiceId
exchangeBeginning = ChoiceId "dir-adausd" oracle
exchangeEnd = ChoiceId "inv-adausd" oracle

decreaseInPrice, increaseInPrice :: ValueId
decreaseInPrice = "Decrease in price"
increaseInPrice = "Increase in price"

initialDeposit :: Party -> Value -> Timeout -> Contract -> Contract -> Contract
initialDeposit by deposit timeout timeoutContinuation continuation =
  When [Case (Deposit by by ada deposit) continuation]
       timeout
       timeoutContinuation

oracleInput :: ChoiceId -> Timeout -> Contract -> Contract -> Contract
oracleInput choiceId timeout timeoutContinuation continuation =
  When [Case (Choice choiceId [Bound 0 100_000_000_000]) continuation]
       timeout
       timeoutContinuation

wait :: Timeout -> Contract -> Contract
wait = When []

gtLtEq :: Value -> Value -> Contract -> Contract -> Contract -> Contract
gtLtEq value1 value2 gtContinuation ltContinuation eqContinuation =
     If (ValueGT value1 value2) gtContinuation
   $ If (ValueLT value1 value2) ltContinuation
                                eqContinuation

recordEndPrice :: ValueId -> ChoiceId -> ChoiceId -> Contract -> Contract
recordEndPrice name choiceId1 choiceId2 =
    Let name (Scale (1%10_000_000_000_000_000) (MulValue priceBeginning (MulValue (ChoiceValue choiceId1) (ChoiceValue choiceId2))))

recordDifference :: ValueId -> Value -> Value -> Contract -> Contract
recordDifference name val1 val2 = Let name (SubValue val1 val2)

transferUpToDeposit :: Party -> Value -> Party -> Value -> Contract -> Contract
transferUpToDeposit from payerDeposit to amount =
   Pay from (Account to) ada (Cond (ValueLT amount payerDeposit) amount payerDeposit)

refund :: Party -> Value -> Contract -> Contract
refund who amount
  | explicitRefunds = Pay who (Party who) ada amount
  | otherwise = id

refundBoth :: Contract
refundBoth = refund party partyDeposit (refund counterparty counterpartyDeposit Close)

refundIfGtZero :: Party -> Value -> Contract -> Contract
refundIfGtZero who amount continuation
  | explicitRefunds = If (ValueGT amount (Constant 0)) (refund who amount continuation) continuation
  | otherwise = continuation

refundUpToBothDeposits :: Party -> Value -> Contract -> Contract
refundUpToBothDeposits who amount
  | explicitRefunds = refund who $ Cond (ValueGT amount bothDeposits) bothDeposits amount
  | otherwise = id

refundAfterDifference :: Party -> Value -> Party -> Value -> Value -> Contract
refundAfterDifference payer payerDeposit payee payeeDeposit difference =
    refundIfGtZero payer (SubValue payerDeposit difference)
  $ refundUpToBothDeposits payee (AddValue payeeDeposit difference)
    Close

contract :: Contract
contract = initialDeposit party partyDeposit (SlotParam "Party deposit deadline") Close
         $ initialDeposit counterparty counterpartyDeposit (SlotParam "Counterparty deposit deadline") (refund party partyDeposit Close)
         $ wait (SlotParam "First window beginning")
         $ oracleInput exchangeBeginning (SlotParam "First window deadline") refundBoth
         $ wait (SlotParam "Second window beginning")
         $ oracleInput exchangeEnd (SlotParam "Second window deadline") refundBoth
         $ recordEndPrice priceEnd exchangeBeginning exchangeEnd
         $ gtLtEq priceBeginning (UseValue priceEnd)
                  ( recordDifference decreaseInPrice priceBeginning (UseValue priceEnd)
                  $ transferUpToDeposit counterparty counterpartyDeposit party (UseValue decreaseInPrice)
                  $ refundAfterDifference counterparty counterpartyDeposit party partyDeposit (UseValue decreaseInPrice)
                  )
                  ( recordDifference increaseInPrice (UseValue priceEnd) priceBeginning
                  $ transferUpToDeposit party partyDeposit counterparty (UseValue increaseInPrice)
                  $ refundAfterDifference party partyDeposit counterparty counterpartyDeposit (UseValue increaseInPrice)
                  )
                  refundBoth
