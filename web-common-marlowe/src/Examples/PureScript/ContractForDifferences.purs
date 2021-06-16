module Examples.PureScript.ContractForDifferences
  ( contractTemplate
  , metaData
  , extendedContract
  ) where

import Prelude
import Data.BigInteger (BigInteger, fromInt)
import Examples.Metadata as Metadata
import Marlowe.Extended (Action(..), Case(..), Contract(..), Observation(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Extended.Metadata (MetaData, ContractTemplate)
import Marlowe.Semantics (Bound(..), ChoiceId(..), Party(..), Token(..), ValueId(..))

contractTemplate :: ContractTemplate
contractTemplate = { metaData, extendedContract }

metaData :: MetaData
metaData = Metadata.contractForDifferences

ada :: Token
ada = Token "" ""

party :: Party
party = Role "Party"

counterparty :: Party
counterparty = Role "Counterparty"

oracle :: Party
oracle = Role "Oracle"

depositAmount :: BigInteger
depositAmount = fromInt 100000000

deposit :: Value
deposit = Constant depositAmount

doubleDeposit :: Value
doubleDeposit = Constant (depositAmount * fromInt 2)

priceBeginning :: ChoiceId
priceBeginning = ChoiceId "Price at beginning" oracle

priceEnd :: ChoiceId
priceEnd = ChoiceId "Price at end" oracle

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
  When [ Case (Choice choiceId [ Bound zero (fromInt 1000000000) ]) continuation ]
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
recordDifference name choiceId1 choiceId2 = Let name (SubValue (ChoiceValue choiceId1) (ChoiceValue choiceId2))

transferUpToDeposit :: Party -> Party -> Value -> Contract -> Contract
transferUpToDeposit from to amount = Pay from (Account to) ada (Cond (ValueLT amount deposit) amount deposit)

extendedContract :: Contract
extendedContract =
  initialDeposit party (Slot $ fromInt 300) Close
    $ initialDeposit counterparty (Slot $ fromInt 600) Close
    $ oracleInput priceBeginning (Slot $ fromInt 900) Close
    $ wait (Slot $ fromInt 1500)
    $ oracleInput priceEnd (Slot $ fromInt 1800) Close
    $ gtLtEq (ChoiceValue priceBeginning) (ChoiceValue priceEnd)
        ( recordDifference decreaseInPrice priceBeginning priceEnd
            $ transferUpToDeposit counterparty party (UseValue decreaseInPrice)
                Close
        )
        ( recordDifference increaseInPrice priceEnd priceBeginning
            $ transferUpToDeposit party counterparty (UseValue increaseInPrice)
                Close
        )
        Close
