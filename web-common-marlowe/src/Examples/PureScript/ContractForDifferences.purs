module Examples.PureScript.ContractForDifferences
  ( contractTemplate
  , metaData
  , defaultSlotContent
  , extendedContract
  ) where

import Prelude
import Data.BigInteger (BigInteger, fromInt)
import Data.Map as Map
import Data.Map (Map)
import Data.Tuple.Nested ((/\))
import Examples.Metadata as Metadata
import Marlowe.Extended (Action(..), Case(..), Contract(..), Observation(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Extended.Metadata (MetaData, ContractTemplate)
import Marlowe.Semantics (Bound(..), ChoiceId(..), Party(..), Token(..), ValueId(..))

contractTemplate :: ContractTemplate
contractTemplate = { metaData, extendedContract }

metaData :: MetaData
metaData = Metadata.contractForDifferences

defaultSlotContent :: Map String BigInteger
defaultSlotContent =
  Map.fromFoldable
    [ "Party deposit deadline" /\ fromInt 300
    , "Counterparty deposit deadline" /\ fromInt 600
    , "First window beginning" /\ fromInt 900
    , "First window deadline" /\ fromInt 1200
    , "Second window beginning" /\ fromInt 1500
    , "Second window deadline" /\ fromInt 1800
    ]

ada :: Token
ada = Token "" ""

party :: Party
party = Role "Party"

counterparty :: Party
counterparty = Role "Counterparty"

oracle :: Party
oracle = Role "Oracle"

partyDeposit :: Value
partyDeposit = ConstantParam "Amount paid by party"

counterpartyDeposit :: Value
counterpartyDeposit = ConstantParam "Amount paid by counterparty"

bothDeposits :: Value
bothDeposits = AddValue partyDeposit counterpartyDeposit

priceBeginning :: ChoiceId
priceBeginning = ChoiceId "Price in first window" oracle

priceEnd :: ChoiceId
priceEnd = ChoiceId "Price in second window" oracle

decreaseInPrice :: ValueId
decreaseInPrice = ValueId "Decrease in price"

increaseInPrice :: ValueId
increaseInPrice = ValueId "Increase in price"

initialDeposit :: Party -> Value -> Timeout -> Contract -> Contract -> Contract
initialDeposit by deposit timeout timeoutContinuation continuation =
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

transferUpToDeposit :: Party -> Value -> Party -> Value -> Contract -> Contract
transferUpToDeposit from payerDeposit to amount = Pay from (Account to) ada (Cond (ValueLT amount payerDeposit) amount payerDeposit)

extendedContract :: Contract
extendedContract =
  initialDeposit party partyDeposit (SlotParam "Party deposit deadline") Close
    $ initialDeposit counterparty counterpartyDeposit (SlotParam "Counterparty deposit deadline") Close
    $ wait (SlotParam "First window beginning")
    $ oracleInput priceBeginning (SlotParam "First window deadline") Close
    $ wait (SlotParam "Second window beginning")
    $ oracleInput priceEnd (SlotParam "Second window deadline") Close
    $ gtLtEq (ChoiceValue priceBeginning) (ChoiceValue priceEnd)
        ( recordDifference decreaseInPrice priceBeginning priceEnd
            $ transferUpToDeposit counterparty counterpartyDeposit party (UseValue decreaseInPrice)
                Close
        )
        ( recordDifference increaseInPrice priceEnd priceBeginning
            $ transferUpToDeposit party partyDeposit counterparty (UseValue increaseInPrice)
                Close
        )
        Close
