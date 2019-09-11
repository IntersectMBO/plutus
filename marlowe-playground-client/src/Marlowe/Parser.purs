module Marlowe.Parser where


import Control.Alternative ((<|>))
import Control.Lazy (fix)
import Data.Array (fromFoldable, many)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.List (List, some)
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits (fromCharArray)
import Marlowe.Semantics (AccountId(..), Action(..), Ada(..), Bound(..), Case(..), ChoiceId(..), Contract(..), Input(..), Observation(..), Party, Payee(..), PubKey, Slot(..), SlotInterval(..), Timeout, TransactionInput(..), TransactionWarning(..), Value(..), ValueId(..))
import Prelude ((*>), (<*), (<*>), bind, const, pure, (<$>), void, ($), (<<<), discard)
import Text.Parsing.Parser (Parser, fail)
import Text.Parsing.Parser.Basic (integral, parens)
import Text.Parsing.Parser.Combinators (between, choice, sepBy)
import Text.Parsing.Parser.String (char, string)
import Text.Parsing.Parser.Token (alphaNum, space)

-- All arguments are space separated so we add **> to reduce boilerplate
maybeSpaces :: Parser String (Array Char)
maybeSpaces = many space

spaces :: Parser String (List Char)
spaces = some space

appRSpaces :: forall a b. Parser String a -> Parser String b -> Parser String b
appRSpaces p q = p *> spaces *> q

infixl 4 appRSpaces as **>

appSpaces :: forall a b. Parser String (a -> b) -> Parser String a -> Parser String b
appSpaces p q = p <*> (spaces *> q)

infixl 4 appSpaces as <**>

text :: Parser String String
text = between (char '"') (char '"') $ fromCharArray <<< fromFoldable <$> many (choice [alphaNum, space])

haskellList :: forall a. Parser String a -> Parser String (List a)
haskellList p = squareParens $ do
  void maybeSpaces
  v <- p `sepBy` (maybeSpaces *> string "," *> maybeSpaces)
  void maybeSpaces
  pure v
  where
    squareParens = between (string "[") (string "]")

maybeParens :: forall a. Parser String a -> Parser String a
maybeParens p = parens p <|> p

array :: forall a. Parser String a -> Parser String (Array a)
array p = Array.fromFoldable <$> haskellList p

----------------------------------------------------------------------
bigInteger :: Parser String BigInteger
bigInteger = do
  i <- integral
  case BigInteger.fromString i of
    (Just v) -> pure v
    Nothing -> fail "not a valid BigInt"

valueId :: Parser String ValueId
valueId = ValueId <$> text

slot :: Parser String Slot
slot = Slot <$> maybeParens bigInteger

timeout :: Parser String Timeout
timeout = slot

accountId :: Parser String AccountId
accountId =
  parens do
    void maybeSpaces
    void $ string "AccountId"
    void spaces
    first <- maybeParens bigInteger
    void spaces
    second <- text
    void maybeSpaces
    pure $ AccountId first second

choiceId :: Parser String ChoiceId
choiceId =
  parens do
    void maybeSpaces
    void $ string "ChoiceId"
    void spaces
    first <- text
    void spaces
    second <- text
    void maybeSpaces
    pure $ ChoiceId first second

atomValue :: Parser String Value
atomValue = pure SlotIntervalStart <* string "SlotIntervalStart"
    <|> pure SlotIntervalEnd <* string "SlotIntervalEnd"

recValue :: Parser String Value
recValue =
  (AvailableMoney <$> (string "AvailableMoney" **> accountId))
    <|> (Constant <$> (string "Constant" **> (maybeParens bigInteger)))
    <|> (NegValue <$> (string "NegValue" **> value'))
    <|> (AddValue <$> (string "AddValue" **> value') <**> value')
    <|> (SubValue <$> (string "SubValue" **> value') <**> value')
    <|> (ChoiceValue <$> (string "ChoiceValue" **> choiceId) <**> value')
    <|> (UseValue <$> (string "UseValue" **> valueId))
  where
  value' :: Parser String Value
  value' = atomValue <|> fix (\p -> parens recValue)

value :: Parser String Value
value = atomValue <|> recValue


atomObservation :: Parser String Observation
atomObservation =
  pure TrueObs <* string "TrueObs"
    <|> pure FalseObs
    <* string "FalseObs"

recObservation :: Parser String Observation
recObservation =
    (AndObs <$> (string "AndObs" **> observation') <**> observation')
    <|> (OrObs <$> (string "OrObs" **> observation') <**> observation')
    <|> (NotObs <$> (string "NotObs" **> observation'))
    <|> (ChoseSomething <$> (string "ChoseSomething" **> choiceId))
    <|> (ValueGE <$> (string "ValueGE" **> value') <**> value')
    <|> (ValueGT <$> (string "ValueGT" **> value') <**> value')
    <|> (ValueLT <$> (string "ValueLT" **> value') <**> value')
    <|> (ValueLE <$> (string "ValueLE" **> value') <**> value')
    <|> (ValueEQ <$> (string "ValueEQ" **> value') <**> value')
  where
  observation' = atomObservation <|> fix \p -> parens recObservation

  value' = atomValue <|> fix (\p -> parens value)

observation :: Parser String Observation
observation = atomObservation <|> recObservation

payee :: Parser String Payee
payee = (Account <$> (string "Account" **> accountId))
        <|> (Party <$> (string "Party" **> text))

pubkey :: Parser String PubKey
pubkey = text

party :: Parser String Party
party = pubkey

bound :: Parser String Bound
bound =
  parens do
    void maybeSpaces
    void $ string "Bound"
    void spaces
    first <- maybeParens bigInteger
    void spaces
    second <- maybeParens bigInteger
    void maybeSpaces
    pure (Bound first second)

action :: Parser String Action
action =
    (Deposit <$> (string "Deposit" **> accountId) <**> party <**> value')
    <|> (Choice <$> (string "Choice" **> choiceId) <**> array bound)
    <|> (Notify <$> (string "Notify" **> observation'))
    where
      observation' = atomObservation <|> fix \p -> parens recObservation
      value' = atomValue <|> fix (\p -> parens recValue)

case' :: Parser String Case
case' = do
    void maybeSpaces
    void $ string "Case"
    void spaces
    first <- parens action
    void spaces
    second <- contract'
    void maybeSpaces
    pure $ (Case first second)
  where
  contract' = atomContract <|> fix \p -> parens recContract

cases :: Parser String (Array Case)
cases = array case'

atomContract :: Parser String Contract
atomContract = pure Refund <* string "Refund"

recContract :: Parser String Contract
recContract =
    ( Pay <$> (string "Pay" **> accountId)
          <**> parens payee
          <**> value'
          <**> contract'
      )
    <|> (If <$> (string "If" **> observation') <**> contract' <**> contract')
    <|> (When <$> (string "When" **> (array (maybeParens case'))) <**> timeout <**> contract')
    <|> (Let <$> (string "Let" **> valueId) <**> value' <**> contract')
    <|> (fail "not a valid Contract")
  where
  contract' = atomContract <|> fix \p -> parens recContract

  observation' = atomObservation <|> fix \p -> parens observation

  value' = atomValue <|> fix (\p -> parens value)

contract :: Parser String Contract
contract = do
  void maybeSpaces
  c <- (atomContract <|> recContract)
  void maybeSpaces
  pure c

testString :: String
testString = """When [
  (Case
     (Deposit
        (AccountId 0 "alice") "alice"
        (Constant 450))
     (When [
           (Case
              (Choice
                 (ChoiceId "1" "alice") [
                 (Bound 0 1)])
              (When [
                 (Case
                    (Choice
                       (ChoiceId "1" "bob") [
                       (Bound 0 1)])
                    (If
                       (ValueEQ
                          (ChoiceValue
                             (ChoiceId "1" "alice")
                             (Constant 42))
                          (ChoiceValue
                             (ChoiceId "1" "bob")
                             (Constant 42)))
                       (If
                          (ValueEQ
                             (ChoiceValue
                                (ChoiceId "1" "alice")
                                (Constant 42))
                             (Constant 0))
                          (Pay
                             (AccountId 0 "alice")
                             (Party "bob")
                             (Constant 450) Refund) Refund)
                       (When [
                             (Case
                                (Choice
                                   (ChoiceId "1" "carol") [
                                   (Bound 1 1)]) Refund)
                             ,
                             (Case
                                (Choice
                                   (ChoiceId "1" "carol") [
                                   (Bound 0 0)])
                                (Pay
                                   (AccountId 0 "alice")
                                   (Party "bob")
                                   (Constant 450) Refund))] 100 Refund)))] 60
                 (When [
                       (Case
                          (Choice
                             (ChoiceId "1" "carol") [
                             (Bound 1 1)]) Refund)
                       ,
                       (Case
                          (Choice
                             (ChoiceId "1" "carol") [
                             (Bound 0 0)])
                          (Pay
                             (AccountId 0 "alice")
                             (Party "bob")
                             (Constant 450) Refund))] 100 Refund)))
           ,
           (Case
              (Choice
                 (ChoiceId "1" "bob") [
                 (Bound 0 1)])
              (When [
                 (Case
                    (Choice
                       (ChoiceId "1" "alice") [
                       (Bound 0 1)])
                    (If
                       (ValueEQ
                          (ChoiceValue
                             (ChoiceId "1" "alice")
                             (Constant 42))
                          (ChoiceValue
                             (ChoiceId "1" "bob")
                             (Constant 42)))
                       (If
                          (ValueEQ
                             (ChoiceValue
                                (ChoiceId "1" "alice")
                                (Constant 42))
                             (Constant 0))
                          (Pay
                             (AccountId 0 "alice")
                             (Party "bob")
                             (Constant 450) Refund) Refund)
                       (When [
                             (Case
                                (Choice
                                   (ChoiceId "1" "carol") [
                                   (Bound 1 1)]) Refund)
                             ,
                             (Case
                                (Choice
                                   (ChoiceId "1" "carol") [
                                   (Bound 0 0)])
                                (Pay
                                   (AccountId 0 "alice")
                                   (Party "bob")
                                   (Constant 450) Refund))] 100 Refund)))] 60
                 (When [
                       (Case
                          (Choice
                             (ChoiceId "1" "carol") [
                             (Bound 1 1)]) Refund)
                       ,
                       (Case
                          (Choice
                             (ChoiceId "1" "carol") [
                             (Bound 0 0)])
                          (Pay
                             (AccountId 0 "alice")
                             (Party "bob")
                             (Constant 450) Refund))] 100 Refund)))] 40 Refund))] 10 Refund"""

input :: Parser String Input
input = 
   (IDeposit <$> (string "IDeposit" **> accountId) <**> party <**> (Lovelace <$> (maybeParens bigInteger)))
   <|> (IChoice <$> (string "IChoice" **> choiceId) <**> (maybeParens bigInteger))
   <|> ((const INotify) <$> (string "INotify"))

inputList :: Parser String (List Input)
inputList = haskellList input

slotInterval :: Parser String SlotInterval
slotInterval = (SlotInterval <$> (string "SlotInterval" **> slot) <**> slot)

transactionInput :: Parser String TransactionInput
transactionInput = 
   do void $ string "TransactionInput"
      void maybeSpaces
      void $ string "{"
      void maybeSpaces
      void $ string "txInterval"
      void maybeSpaces
      void $ string "="
      void maybeSpaces
      interval <- slotInterval
      void maybeSpaces
      void $ string ","
      void maybeSpaces
      void $ string "txInputs"
      void maybeSpaces
      void $ string "="
      void maybeSpaces
      inputs <- inputList
      void maybeSpaces
      void $ string "}"
      pure $ TransactionInput { interval, inputs }

transactionInputList :: Parser String (List TransactionInput)
transactionInputList = haskellList transactionInput

testTransactionInputParsing :: String
testTransactionInputParsing = "[TransactionInput {txInterval = SlotInterval (-5) (-4), txInputs = [IDeposit (AccountId 1 \"Alice\") \"Bob\" 20,INotify]}]"

transactionWarning :: Parser String TransactionWarning
transactionWarning = (TransactionNonPositiveDeposit <$> (string "TransactionNonPositiveDeposit" **> party) <**> accountId <**> (Lovelace <$> (maybeParens bigInteger)))
                 <|> (TransactionNonPositivePay <$> (string "TransactionNonPositivePay" **> accountId) <**> (parens payee) <**> (Lovelace <$> (maybeParens bigInteger)))
                 <|> (TransactionPartialPay <$> (string "TransactionPartialPay" **> accountId) <**> (parens payee) <**> (Lovelace <$> (maybeParens bigInteger)) <**> (Lovelace <$> (maybeParens bigInteger)))
                 <|> (TransactionShadowing <$> (string "TransactionShadowing" **> valueId) <**> (maybeParens bigInteger) <**> (maybeParens bigInteger))

transactionWarningList :: Parser String (List TransactionWarning)
transactionWarningList = haskellList transactionWarning

testTransactionWarningParsing :: String
testTransactionWarningParsing = "[TransactionNonPositivePay (AccountId 1 \"Bob\") (Party \"Bob\") (-10),TransactionPartialPay (AccountId 1 \"Bob\") (Party \"Alice\") 0 21]"
