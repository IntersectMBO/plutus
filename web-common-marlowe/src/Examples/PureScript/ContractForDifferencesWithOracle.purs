module Examples.PureScript.ContractForDifferencesWithOracle
  ( contractTemplate
  , metaData
  , extendedContract
  ) where

import Prelude
import Data.BigInteger (BigInteger, fromInt)
import Examples.Metadata as Metadata
import Marlowe.Extended (Action(..), Case(..), Contract(..), Observation(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Extended.Metadata (MetaData, ContractTemplate)
import Marlowe.Semantics (Bound(..), ChoiceId(..), Party(..), Rational(..), Token(..), ValueId(..))

contractTemplate :: ContractTemplate
contractTemplate = { metaData, extendedContract }

metaData :: MetaData
metaData = Metadata.contractForDifferencesWithOracle

ada :: Token
ada = Token "" ""

party :: Party
party = Role "Party"

counterparty :: Party
counterparty = Role "Counterparty"

oracle :: Party
oracle = Role "kraken"

depositAmount :: BigInteger
depositAmount = fromInt 100000000

deposit :: Value
deposit = Constant depositAmount

doubleDeposit :: Value
doubleDeposit = Constant (depositAmount * fromInt 2)

priceBeginning :: Value
priceBeginning = Constant (fromInt 100000000)

priceEnd :: ValueId
priceEnd = ValueId "Price at end"

exchangeBeginning :: ChoiceId
exchangeBeginning = ChoiceId "dir-adausd" oracle

exchangeEnd :: ChoiceId
exchangeEnd = ChoiceId "inv-adausd" oracle

decreaseInPrice :: ValueId
decreaseInPrice = ValueId "Decrease in price"

increaseInPrice :: ValueId
increaseInPrice = ValueId "Increase in price"

initialDeposit :: Party -> Timeout -> Contract -> Contract -> Contract
initialDeposit by timeout timeoutContinuation continuation =
  When [ Case (Deposit by by ada deposit) continuation ]
    timeout
    timeoutContinuation

oracleInput :: ChoiceId -> Timeout -> Contract -> Contract -> Contract
oracleInput choiceId timeout timeoutContinuation continuation =
  When [ Case (Choice choiceId [ Bound zero (fromInt 100000 * fromInt 1000000) ]) continuation ]
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
recordEndPrice name choiceId1 choiceId2 = Let name (Scale (Rational one (fromInt 100000000)) (MulValue (ChoiceValue choiceId1) (ChoiceValue choiceId2)))

recordDifference :: ValueId -> Value -> Value -> Contract -> Contract
recordDifference name val1 val2 = Let name (SubValue val1 val2)

transferUpToDeposit :: Party -> Party -> Value -> Contract -> Contract
transferUpToDeposit from to amount = Pay from (Account to) ada (Cond (ValueLT amount deposit) amount deposit)

extendedContract :: Contract
extendedContract =
  initialDeposit party (Slot $ fromInt 30) Close
    $ initialDeposit counterparty (Slot $ fromInt 60) Close
    $ oracleInput exchangeBeginning (Slot $ fromInt 90) Close
    $ wait (Slot $ fromInt 150)
    $ oracleInput exchangeEnd (Slot $ fromInt 180) Close
    $ recordEndPrice priceEnd exchangeBeginning exchangeEnd
    $ gtLtEq priceBeginning (UseValue priceEnd)
        ( recordDifference decreaseInPrice priceBeginning (UseValue priceEnd)
            $ transferUpToDeposit counterparty party (UseValue decreaseInPrice)
                Close
        )
        ( recordDifference increaseInPrice (UseValue priceEnd) priceBeginning
            $ transferUpToDeposit party counterparty (UseValue increaseInPrice)
                Close
        )
        Close
