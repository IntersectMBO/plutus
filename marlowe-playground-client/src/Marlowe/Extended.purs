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
import Text.Pretty (class Args, class Pretty, genericHasArgs, genericHasNestedArgs, genericPretty, pretty)

class ToCore a b where
  toCore :: a -> Maybe b

data Timeout
  = SlotParam String
  | Slot BigInteger

derive instance genericTimeout :: Generic Timeout _

derive instance eqTimeout :: Eq Timeout

derive instance ordTimeout :: Ord Timeout

instance encodeJsonTimeout :: Encode Timeout where
  encode (SlotParam str) = encode { slot_param: str }
  encode (Slot val) = encode val

instance decodeJsonTimeout :: Decode Timeout where
  decode a =
    ( SlotParam <$> decodeProp "slot_param" a
        <|> (Slot <$> decode a)
    )

instance showTimeout :: Show Timeout where
  show (Slot x) = show x
  show v = genericShow v

instance prettyTimeout :: Pretty Timeout where
  pretty (Slot x) = pretty x
  pretty v = genericPretty v

instance hasArgsTimeout :: Args Timeout where
  hasArgs (Slot _) = false
  hasArgs x = genericHasArgs x
  hasNestedArgs (Slot _) = false
  hasNestedArgs x = genericHasNestedArgs x

instance toCoreTimeout :: ToCore Timeout S.Slot where
  toCore (SlotParam _) = Nothing
  toCore (Slot x) = Just (S.Slot x)

data Value
  = AvailableMoney S.AccountId S.Token
  | Constant BigInteger
  | ConstantParam String
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
  encode (ConstantParam str) = encode { constant_param: str }
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
      <|> ( ConstantParam <$> decodeProp "constant_param" a
        )
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

instance toCoreValue :: ToCore Value S.Value where
  toCore (Constant c) = Just $ S.Constant c
  toCore (ConstantParam _) = Nothing
  toCore (AvailableMoney accId tok) = S.AvailableMoney <$> pure accId <*> pure tok
  toCore (NegValue v) = S.NegValue <$> toCore v
  toCore (AddValue lhs rhs) = S.AddValue <$> toCore lhs <*> toCore rhs
  toCore (SubValue lhs rhs) = S.SubValue <$> toCore lhs <*> toCore rhs
  toCore (MulValue lhs rhs) = S.MulValue <$> toCore lhs <*> toCore rhs
  toCore (Scale f v) = S.Scale <$> pure f <*> toCore v
  toCore (ChoiceValue choId) = Just $ S.ChoiceValue choId
  toCore SlotIntervalStart = Just $ S.SlotIntervalStart
  toCore SlotIntervalEnd = Just $ S.SlotIntervalEnd
  toCore (UseValue vId) = Just $ S.UseValue vId
  toCore (Cond obs lhs rhs) = S.Cond <$> toCore obs <*> toCore lhs <*> toCore rhs

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

instance toCoreObservation :: ToCore Observation S.Observation where
  toCore (AndObs lhs rhs) = S.AndObs <$> toCore lhs <*> toCore rhs
  toCore (OrObs lhs rhs) = S.OrObs <$> toCore lhs <*> toCore rhs
  toCore (NotObs v) = S.NotObs <$> toCore v
  toCore (ChoseSomething choId) = Just $ S.ChoseSomething choId
  toCore (ValueGE lhs rhs) = S.ValueGE <$> toCore lhs <*> toCore rhs
  toCore (ValueGT lhs rhs) = S.ValueGT <$> toCore lhs <*> toCore rhs
  toCore (ValueLT lhs rhs) = S.ValueLT <$> toCore lhs <*> toCore rhs
  toCore (ValueLE lhs rhs) = S.ValueLE <$> toCore lhs <*> toCore rhs
  toCore (ValueEQ lhs rhs) = S.ValueEQ <$> toCore lhs <*> toCore rhs
  toCore TrueObs = Just S.TrueObs
  toCore FalseObs = Just S.FalseObs

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

instance toCoreAction :: ToCore Action S.Action where
  toCore (Deposit accId party tok val) = S.Deposit <$> pure accId <*> pure party <*> pure tok <*> toCore val
  toCore (Choice choId bounds) = Just $ S.Choice choId bounds
  toCore (Notify obs) = S.Notify <$> toCore obs

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

instance toCorePayee :: ToCore Payee S.Payee where
  toCore (Account accId) = Just $ S.Account accId
  toCore (Party roleName) = Just $ S.Party roleName

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

instance toCoreCase :: ToCore Case S.Case where
  toCore (Case act c) = S.Case <$> toCore act <*> toCore c

data Contract
  = Close
  | Pay S.AccountId Payee S.Token Value Contract
  | If Observation Contract Contract
  | When (Array Case) Timeout Contract
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

instance toCoreContract :: ToCore Contract S.Contract where
  toCore Close = Just S.Close
  toCore (Pay accId payee tok val cont) = S.Pay <$> pure accId <*> toCore payee <*> pure tok <*> toCore val <*> toCore cont
  toCore (If obs cont1 cont2) = S.If <$> toCore obs <*> toCore cont1 <*> toCore cont2
  toCore (When cases tim cont) = S.When <$> traverse toCore cases <*> toCore tim <*> toCore cont
  toCore (Let varId val cont) = S.Let <$> pure varId <*> toCore val <*> toCore cont
  toCore (Assert obs cont) = S.Assert <$> toCore obs <*> toCore cont
