module Marlowe.Extended where

import Prelude
import Control.Alt ((<|>))
import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Foreign (ForeignError(..), fail)
import Foreign.Class (class Encode, class Decode, encode, decode)
import Foreign.Index (hasProperty)
import Marlowe.Semantics (decodeProp)
import Marlowe.Semantics as S
import Text.Pretty (class Args, class Pretty, genericHasArgs, genericHasNestedArgs, genericPretty)

data Value
  = AvailableMoney S.AccountId S.Token
  | Constant BigInteger
  | NegValue Value
  | AddValue Value Value
  | SubValue Value Value
  | MulValue Value Value
  | Scale S.Rational Value
  | ChoiceValue S.ChoiceId
  | SlotIntervalStart
  | SlotIntervalEnd
  | UseValue S.ValueId
  | Cond Observation Value Value

derive instance genericValue :: Generic Value _

derive instance eqValue :: Eq Value

derive instance ordValue :: Ord Value

instance encodeJsonValue :: Encode Value where
  encode (AvailableMoney accId tok) =
    encode
      { amount_of_token: tok
      , in_account: accId
      }
  encode (Constant val) = encode val
  encode (NegValue val) =
    encode
      { negate: val
      }
  encode (AddValue lhs rhs) =
    encode
      { add: lhs
      , and: rhs
      }
  encode (SubValue lhs rhs) =
    encode
      { value: lhs
      , minus: rhs
      }
  encode (MulValue lhs rhs) =
    encode
      { multiply: lhs
      , times: rhs
      }
  encode (Scale (S.Rational num den) val) =
    encode
      { multiply: val
      , times: num
      , divide_by: den
      }
  encode (ChoiceValue choiceId) =
    encode
      { value_of_choice: choiceId
      }
  encode SlotIntervalStart = encode "slot_interval_start"
  encode SlotIntervalEnd = encode "slot_interval_end"
  encode (UseValue valueId) =
    encode
      { use_value: valueId
      }
  encode (Cond cond thenValue elseValue) =
    encode
      { if: cond
      , then: thenValue
      , else: elseValue
      }

instance decodeJsonValue :: Decode Value where
  decode a =
    ( ifM ((\x -> x == "slot_interval_start") <$> decode a)
        (pure SlotIntervalStart)
        (fail (ForeignError "Not \"slot_interval_start\" string"))
    )
      <|> ( ifM ((\x -> x == "slot_interval_end") <$> decode a)
            (pure SlotIntervalEnd)
            (fail (ForeignError "Not \"slot_interval_end\" string"))
        )
      <|> ( AvailableMoney <$> decodeProp "in_account" a
            <*> decodeProp "amount_of_token" a
        )
      <|> (Constant <$> decode a)
      <|> (NegValue <$> decodeProp "negate" a)
      <|> ( AddValue <$> decodeProp "add" a
            <*> decodeProp "and" a
        )
      <|> ( SubValue <$> decodeProp "value" a
            <*> decodeProp "minus" a
        )
      <|> ( if (hasProperty "divide_by" a) then
            ( Scale
                <$> ( S.Rational <$> decodeProp "times" a
                      <*> decodeProp "divide_by" a
                  )
                <*> decodeProp "multiply" a
            )
          else
            ( MulValue <$> decodeProp "multiply" a
                <*> decodeProp "times" a
            )
        )
      <|> (ChoiceValue <$> decodeProp "value_of_choice" a)
      <|> (UseValue <$> decodeProp "use_value" a)
      <|> ( Cond <$> decodeProp "if" a
            <*> decodeProp "then" a
            <*> decodeProp "else" a
        )

instance showValue :: Show Value where
  show v = genericShow v

instance prettyValue :: Pretty Value where
  pretty v = genericPretty v

instance hasArgsValue :: Args Value where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

data Observation
  = AndObs Observation Observation
  | OrObs Observation Observation
  | NotObs Observation
  | ChoseSomething S.ChoiceId
  | ValueGE Value Value
  | ValueGT Value Value
  | ValueLT Value Value
  | ValueLE Value Value
  | ValueEQ Value Value
  | TrueObs
  | FalseObs

derive instance genericObservation :: Generic Observation _

derive instance eqObservation :: Eq Observation

derive instance ordObservation :: Ord Observation

instance encodeJsonObservation :: Encode Observation where
  encode (AndObs lhs rhs) =
    encode
      { both: lhs
      , and: rhs
      }
  encode (OrObs lhs rhs) =
    encode
      { either: lhs
      , or: rhs
      }
  encode (NotObs obs) =
    encode
      { not: obs
      }
  encode (ChoseSomething choiceId) =
    encode
      { chose_something_for: choiceId
      }
  encode (ValueGE lhs rhs) =
    encode
      { value: lhs
      , ge_than: rhs
      }
  encode (ValueGT lhs rhs) =
    encode
      { value: lhs
      , gt: rhs
      }
  encode (ValueLT lhs rhs) =
    encode
      { value: lhs
      , lt: rhs
      }
  encode (ValueLE lhs rhs) =
    encode
      { value: lhs
      , le_than: rhs
      }
  encode (ValueEQ lhs rhs) =
    encode
      { value: lhs
      , equal_to: rhs
      }
  encode TrueObs = encode true
  encode FalseObs = encode false

instance decodeJsonObservation :: Decode Observation where
  decode a =
    ( ifM (decode a)
        (pure TrueObs)
        (fail (ForeignError "Not a boolean"))
    )
      <|> ( ifM (not <$> decode a)
            (pure FalseObs)
            (fail (ForeignError "Not a boolean"))
        )
      <|> ( AndObs <$> decodeProp "both" a
            <*> decodeProp "and" a
        )
      <|> ( OrObs <$> decodeProp "either" a
            <*> decodeProp "or" a
        )
      <|> (NotObs <$> decodeProp "not" a)
      <|> (ChoseSomething <$> decodeProp "chose_something_for" a)
      <|> ( ValueGE <$> decodeProp "value" a
            <*> decodeProp "ge_than" a
        )
      <|> ( ValueGT <$> decodeProp "value" a
            <*> decodeProp "gt" a
        )
      <|> ( ValueLT <$> decodeProp "value" a
            <*> decodeProp "lt" a
        )
      <|> ( ValueLE <$> decodeProp "value" a
            <*> decodeProp "le_than" a
        )
      <|> ( ValueEQ <$> decodeProp "value" a
            <*> decodeProp "equal_to" a
        )

instance showObservation :: Show Observation where
  show o = genericShow o

instance prettyObservation :: Pretty Observation where
  pretty v = genericPretty v

instance hasArgsObservation :: Args Observation where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

data Action
  = Deposit S.AccountId S.Party S.Token Value
  | Choice S.ChoiceId (Array S.Bound)
  | Notify Observation

derive instance genericAction :: Generic Action _

derive instance eqAction :: Eq Action

derive instance ordAction :: Ord Action

instance encodeJsonAction :: Encode Action where
  encode (Deposit accountId party token value) =
    encode
      { party: party
      , deposits: value
      , of_token: token
      , into_account: accountId
      }
  encode (Choice choiceId boundArray) =
    encode
      { choose_between: boundArray
      , for_choice: choiceId
      }
  encode (Notify obs) =
    encode
      { notify_if: obs
      }

instance decodeJsonAction :: Decode Action where
  decode a =
    ( Deposit <$> decodeProp "into_account" a
        <*> decodeProp "party" a
        <*> decodeProp "of_token" a
        <*> decodeProp "deposits" a
    )
      <|> ( Choice <$> decodeProp "for_choice" a
            <*> decodeProp "choose_between" a
        )
      <|> (Notify <$> decodeProp "notify_if" a)

instance showAction :: Show Action where
  show (Choice cid bounds) = "(Choice " <> show cid <> " " <> show bounds <> ")"
  show v = genericShow v

instance prettyAction :: Pretty Action where
  pretty v = genericPretty v

instance hasArgsAction :: Args Action where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

data Payee
  = Account S.AccountId
  | Party S.Party

derive instance genericPayee :: Generic Payee _

derive instance eqPayee :: Eq Payee

derive instance ordPayee :: Ord Payee

instance encodeJsonPayee :: Encode Payee where
  encode (Account accountId) = encode { account: accountId }
  encode (Party party) = encode { party: party }

instance decodeJsonPayee :: Decode Payee where
  decode a =
    (Account <$> decodeProp "account" a)
      <|> (Party <$> decodeProp "party" a)

instance showPayee :: Show Payee where
  show v = genericShow v

instance prettyPayee :: Pretty Payee where
  pretty v = genericPretty v

instance hasArgsPayee :: Args Payee where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

data Case
  = Case Action Contract

derive instance genericCase :: Generic Case _

derive instance eqCase :: Eq Case

derive instance ordCase :: Ord Case

instance encodeJsonCase :: Encode Case where
  encode (Case action cont) =
    encode
      { case: action
      , then: cont
      }

instance decodeJsonCase :: Decode Case where
  decode a =
    ( Case <$> decodeProp "case" a
        <*> decodeProp "then" a
    )

instance showCase :: Show Case where
  show (Case action contract) = "Case " <> show action <> " " <> show contract

instance prettyCase :: Pretty Case where
  pretty v = genericPretty v

instance hasArgsCase :: Args Case where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

data Contract
  = Close
  | Pay S.AccountId Payee S.Token Value Contract
  | If Observation Contract Contract
  | When (Array Case) S.Timeout Contract
  | Let S.ValueId Value Contract
  | Assert Observation Contract

derive instance genericContract :: Generic Contract _

derive instance eqContract :: Eq Contract

derive instance ordContract :: Ord Contract

instance encodeJsonContract :: Encode Contract where
  encode Close = encode "close"
  encode (Pay accId payee token val cont) =
    encode
      { pay: val
      , token: token
      , from_account: accId
      , to: payee
      , then: cont
      }
  encode (If obs contTrue contFalse) =
    encode
      { if: obs
      , then: contTrue
      , else: contFalse
      }
  encode (When cases timeout cont) =
    encode
      { when: cases
      , timeout: timeout
      , timeout_continuation: cont
      }
  encode (Let valId val cont) =
    encode
      { let: valId
      , be: val
      , then: cont
      }
  encode (Assert obs cont) =
    encode
      { assert: obs
      , then: cont
      }

instance decodeJsonContract :: Decode Contract where
  decode a =
    ( ifM ((\x -> x == "close") <$> decode a)
        (pure Close)
        (fail (ForeignError "Not \"close\" string"))
    )
      <|> ( Pay <$> decodeProp "from_account" a
            <*> decodeProp "to" a
            <*> decodeProp "token" a
            <*> decodeProp "pay" a
            <*> decodeProp "then" a
        )
      <|> ( If <$> decodeProp "if" a
            <*> decodeProp "then" a
            <*> decodeProp "else" a
        )
      <|> ( When <$> decodeProp "when" a
            <*> decodeProp "timeout" a
            <*> decodeProp "timeout_continuation" a
        )
      <|> ( Let <$> decodeProp "let" a
            <*> decodeProp "be" a
            <*> decodeProp "then" a
        )
      <|> ( Assert <$> decodeProp "assert" a
            <*> decodeProp "then" a
        )

instance showContract :: Show Contract where
  show v = genericShow v

instance prettyContract :: Pretty Contract where
  pretty v = genericPretty v

instance hasArgsContract :: Args Contract where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

convertPayeeIfNoExtensions :: Payee -> Maybe S.Payee
convertPayeeIfNoExtensions (Account accId) = Just $ S.Account accId

convertPayeeIfNoExtensions (Party roleName) = Just $ S.Party roleName

convertValueIfNoExtensions :: Value -> Maybe S.Value
convertValueIfNoExtensions (Constant c) = Just $ S.Constant c

convertValueIfNoExtensions (AvailableMoney accId tok) = S.AvailableMoney <$> pure accId <*> pure tok

convertValueIfNoExtensions (NegValue v) = S.NegValue <$> convertValueIfNoExtensions v

convertValueIfNoExtensions (AddValue lhs rhs) = S.AddValue <$> convertValueIfNoExtensions lhs <*> convertValueIfNoExtensions rhs

convertValueIfNoExtensions (SubValue lhs rhs) = S.SubValue <$> convertValueIfNoExtensions lhs <*> convertValueIfNoExtensions rhs

convertValueIfNoExtensions (MulValue lhs rhs) = S.MulValue <$> convertValueIfNoExtensions lhs <*> convertValueIfNoExtensions rhs

convertValueIfNoExtensions (Scale f v) = S.Scale <$> pure f <*> convertValueIfNoExtensions v

convertValueIfNoExtensions (ChoiceValue choId) = Just $ S.ChoiceValue choId

convertValueIfNoExtensions SlotIntervalStart = Just $ S.SlotIntervalStart

convertValueIfNoExtensions SlotIntervalEnd = Just $ S.SlotIntervalEnd

convertValueIfNoExtensions (UseValue vId) = Just $ S.UseValue vId

convertValueIfNoExtensions (Cond obs lhs rhs) = S.Cond <$> convertObservationIfNoExtensions obs <*> convertValueIfNoExtensions lhs <*> convertValueIfNoExtensions rhs

convertObservationIfNoExtensions :: Observation -> Maybe S.Observation
convertObservationIfNoExtensions (AndObs lhs rhs) = S.AndObs <$> convertObservationIfNoExtensions lhs <*> convertObservationIfNoExtensions rhs

convertObservationIfNoExtensions (OrObs lhs rhs) = S.OrObs <$> convertObservationIfNoExtensions lhs <*> convertObservationIfNoExtensions rhs

convertObservationIfNoExtensions (NotObs v) = S.NotObs <$> convertObservationIfNoExtensions v

convertObservationIfNoExtensions (ChoseSomething choId) = Just $ S.ChoseSomething choId

convertObservationIfNoExtensions (ValueGE lhs rhs) = S.ValueGE <$> convertValueIfNoExtensions lhs <*> convertValueIfNoExtensions rhs

convertObservationIfNoExtensions (ValueGT lhs rhs) = S.ValueGT <$> convertValueIfNoExtensions lhs <*> convertValueIfNoExtensions rhs

convertObservationIfNoExtensions (ValueLT lhs rhs) = S.ValueLT <$> convertValueIfNoExtensions lhs <*> convertValueIfNoExtensions rhs

convertObservationIfNoExtensions (ValueLE lhs rhs) = S.ValueLE <$> convertValueIfNoExtensions lhs <*> convertValueIfNoExtensions rhs

convertObservationIfNoExtensions (ValueEQ lhs rhs) = S.ValueEQ <$> convertValueIfNoExtensions lhs <*> convertValueIfNoExtensions rhs

convertObservationIfNoExtensions TrueObs = Just S.TrueObs

convertObservationIfNoExtensions FalseObs = Just S.FalseObs

convertActionIfNoExtensions :: Action -> Maybe S.Action
convertActionIfNoExtensions (Deposit accId party tok val) = S.Deposit <$> pure accId <*> pure party <*> pure tok <*> convertValueIfNoExtensions val

convertActionIfNoExtensions (Choice choId bounds) = Just $ S.Choice choId bounds

convertActionIfNoExtensions (Notify obs) = S.Notify <$> convertObservationIfNoExtensions obs

convertCaseIfNoExtensions :: Case -> Maybe S.Case
convertCaseIfNoExtensions (Case act c) = S.Case <$> convertActionIfNoExtensions act <*> convertContractIfNoExtensions c

convertContractIfNoExtensions :: Contract -> Maybe S.Contract
convertContractIfNoExtensions Close = Just S.Close

convertContractIfNoExtensions (Pay accId payee tok val cont) = S.Pay <$> pure accId <*> convertPayeeIfNoExtensions payee <*> pure tok <*> convertValueIfNoExtensions val <*> convertContractIfNoExtensions cont

convertContractIfNoExtensions (If obs cont1 cont2) = S.If <$> convertObservationIfNoExtensions obs <*> convertContractIfNoExtensions cont1 <*> convertContractIfNoExtensions cont2

convertContractIfNoExtensions (When cases tim cont) = S.When <$> traverse convertCaseIfNoExtensions cases <*> pure tim <*> convertContractIfNoExtensions cont

convertContractIfNoExtensions (Let varId val cont) = S.Let <$> pure varId <*> convertValueIfNoExtensions val <*> convertContractIfNoExtensions cont

convertContractIfNoExtensions (Assert obs cont) = S.Assert <$> convertObservationIfNoExtensions obs <*> convertContractIfNoExtensions cont
