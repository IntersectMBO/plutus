module Marlowe.Parser where

import Control.Alternative ((<|>))
import Control.Lazy (fix)
import Control.Monad.State as MonadState
import Data.Array (fromFoldable, many)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Either (Either)
import Data.List (List, some)
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits (fromCharArray)
import Marlowe.Holes (class FromTerm, AccountId(..), Action(..), Bound(..), Case(..), ChoiceId(..), Contract(..), Observation(..), Party(..), Payee(..), Term(..), Token(..), Value(..), ValueId(..), fromTerm)
import Marlowe.Semantics (CurrencySymbol, PubKey, Slot(..), SlotInterval(..), Timeout, TransactionInput(..), TransactionWarning(..), TokenName)
import Marlowe.Semantics as S
import Prelude (bind, const, discard, flip, pure, show, void, ($), (*>), (<$>), (<*), (<*>), (<<<))
import Text.Parsing.Parser (ParseState(..), Parser, fail, runParser)
import Text.Parsing.Parser.Basic (integral, parens)
import Text.Parsing.Parser.Combinators (between, choice, sepBy)
import Text.Parsing.Parser.String (char, string)
import Text.Parsing.Parser.Token (alphaNum, space)
import Type.Proxy (Proxy(..))

parse :: forall a. Parser String a -> String -> Either String a
parse p = lmap show <<< flip runParser (parens p <|> p)

parseToValue :: forall a b. FromTerm a b => Parser String a -> Parser String b
parseToValue p = do
  v <- p
  let
    mV = fromTerm v
  case mV of
    (Just a) -> pure a
    _ -> fail "Found a hole but was expecting terms only"

hole :: forall a. Parser String (Term a)
hole = do
  (ParseState _ start _) <- MonadState.get
  name <- fromCharArray <$> (char '?' *> many nameChars)
  (ParseState _ end _) <- MonadState.get
  pure $ Hole name Proxy start end
  where
  nameChars = alphaNum <|> char '_'

parseTerm :: forall a. Parser String a -> Parser String (Term a)
parseTerm p = hole <|> (Term <$> p)

maybeSpaces :: Parser String (Array Char)
maybeSpaces = many space

spaces :: Parser String (List Char)
spaces = some space

-- All arguments are space separated so we add **> to reduce boilerplate
appRSpaces :: forall a b. Parser String a -> Parser String b -> Parser String b
appRSpaces p q = p *> spaces *> q

infixl 4 appRSpaces as **>

appSpaces :: forall a b. Parser String (a -> b) -> Parser String a -> Parser String b
appSpaces p q = p <*> (spaces *> q)

infixl 4 appSpaces as <**>

text :: Parser String String
text = between (char '"') (char '"') $ fromCharArray <<< fromFoldable <$> many (choice [ alphaNum, space ])

squareParens :: forall a. Parser String a -> Parser String a
squareParens = between (string "[") (string "]")

haskellList :: forall a. Parser String a -> Parser String (List a)
haskellList p = squareParens (trim p `sepBy` string ",")

trim :: forall a. Parser String a -> Parser String a
trim p = do
  void maybeSpaces
  v <- p
  void maybeSpaces
  pure v

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

bigIntegerTerm :: Parser String (Term BigInteger)
bigIntegerTerm = parseTerm bigInteger

valueId :: Parser String ValueId
valueId = ValueId <$> text

slot :: Parser String Slot
slot = Slot <$> maybeParens bigInteger

slotTerm :: Parser String (Term Slot)
slotTerm = parseTerm slot

timeout :: Parser String Timeout
timeout = slot

accountId :: Parser String AccountId
accountId =
  parens do
    void maybeSpaces
    void $ string "AccountId"
    void spaces
    first <- parseTerm $ maybeParens bigInteger
    void spaces
    second <- parseTerm $ parens party
    void maybeSpaces
    pure $ AccountId first second

choiceId :: Parser String ChoiceId
choiceId =
  parens do
    void maybeSpaces
    void $ string "ChoiceId"
    void spaces
    first <- parseTerm text
    void spaces
    second <- parseTerm $ parens party
    void maybeSpaces
    pure $ ChoiceId first second

atomValue :: Parser String Value
atomValue =
  (pure SlotIntervalStart <* string "SlotIntervalStart")
    <|> (pure SlotIntervalEnd <* string "SlotIntervalEnd")

recValue :: Parser String Value
recValue =
  (AvailableMoney <$> (string "AvailableMoney" **> parseTerm accountId) <**> parseTerm token)
    <|> (Constant <$> (string "Constant" **> bigIntegerTerm))
    <|> (NegValue <$> (string "NegValue" **> value'))
    <|> (AddValue <$> (string "AddValue" **> value') <**> value')
    <|> (SubValue <$> (string "SubValue" **> value') <**> value')
    <|> (ChoiceValue <$> (string "ChoiceValue" **> parseTerm choiceId) <**> value')
    <|> (UseValue <$> (string "UseValue" **> parseTerm valueId))
  where
  value' = parseTerm $ atomValue <|> fix (\p -> parens recValue)

value :: Parser String Value
value = atomValue <|> recValue

atomObservation :: Parser String Observation
atomObservation =
  (pure TrueObs <* string "TrueObs")
    <|> (pure FalseObs <* string "FalseObs")

recObservation :: Parser String Observation
recObservation =
  (AndObs <$> (string "AndObs" **> observation') <**> observation')
    <|> (OrObs <$> (string "OrObs" **> observation') <**> observation')
    <|> (NotObs <$> (string "NotObs" **> observation'))
    <|> (ChoseSomething <$> (string "ChoseSomething" **> parseTerm choiceId))
    <|> (ValueGE <$> (string "ValueGE" **> value') <**> value')
    <|> (ValueGT <$> (string "ValueGT" **> value') <**> value')
    <|> (ValueLT <$> (string "ValueLT" **> value') <**> value')
    <|> (ValueLE <$> (string "ValueLE" **> value') <**> value')
    <|> (ValueEQ <$> (string "ValueEQ" **> value') <**> value')
  where
  observation' = parseTerm $ atomObservation <|> fix \p -> parens recObservation

  value' = parseTerm $ atomValue <|> fix (\p -> parens value)

observation :: Parser String Observation
observation = atomObservation <|> recObservation

payee :: Parser String Payee
payee =
  (Account <$> (string "Account" **> parseTerm accountId))
    <|> (Party <$> (string "Party" **> parseTerm (parens party)))

pubkey :: Parser String PubKey
pubkey = text

party :: Parser String Party
party =
  (PK <$> (string "PK" **> parseTerm pubkey))
    <|> (Role <$> (string "Role" **> parseTerm tokenName))

currencySymbol :: Parser String CurrencySymbol
currencySymbol = text

tokenName :: Parser String TokenName
tokenName = text

token :: Parser String Token
token =
  parens do
    void maybeSpaces
    void $ string "Token"
    void spaces
    first <- parseTerm text
    void spaces
    second <- parseTerm text
    void maybeSpaces
    pure $ Token first second

bound :: Parser String Bound
bound = do
  void maybeSpaces
  void $ string "Bound"
  void spaces
  first <- parseTerm $ maybeParens bigInteger
  void spaces
  second <- parseTerm $ maybeParens bigInteger
  void maybeSpaces
  pure (Bound first second)

action :: Parser String Action
action =
  (Deposit <$> (string "Deposit" **> parseTerm accountId) <**> parseTerm (parens party) <**> parseTerm token <**> value')
    <|> (Choice <$> (string "Choice" **> parseTerm choiceId) <**> array (maybeParens (parseTerm bound)))
    <|> (Notify <$> (string "Notify" **> observation'))
  where
  observation' = parseTerm $ atomObservation <|> fix \p -> parens recObservation

  value' = parseTerm $ atomValue <|> fix (\p -> parens recValue)

case' :: Parser String Case
case' = do
  void maybeSpaces
  void $ string "Case"
  void spaces
  first <- parseTerm $ parens action
  void spaces
  second <- parseTerm contract'
  void maybeSpaces
  pure $ Case first second
  where
  contract' = atomContract <|> fix \p -> parens recContract

cases :: Parser String (Array Case)
cases = array case'

atomContract :: Parser String Contract
atomContract = pure Close <* string "Close"

recContract :: Parser String Contract
recContract =
  ( Pay <$> (string "Pay" **> parseTerm accountId)
      <**> parseTerm (parens payee)
      <**> parseTerm token
      <**> value'
      <**> contract'
  )
    <|> (If <$> (string "If" **> observation') <**> contract' <**> contract')
    <|> (When <$> (string "When" **> (array (maybeParens (parseTerm case')))) <**> parseTerm timeout <**> contract')
    <|> (Let <$> (string "Let" **> parseTerm valueId) <**> value' <**> contract')
    <|> (fail "not a valid Contract")
  where
  contract' = parseTerm $ atomContract <|> fix \p -> parens recContract

  observation' = parseTerm $ atomObservation <|> fix \p -> parens observation

  value' = parseTerm $ atomValue <|> fix (\p -> parens value)

contract :: Parser String Contract
contract = do
  void maybeSpaces
  c <- (atomContract <|> recContract)
  void maybeSpaces
  pure c

contractValue :: Parser String S.Contract
contractValue = parseToValue contract

testString :: String
testString =
  """When [
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
                             (Constant 450) Close) Close)
                       (When [
                             (Case
                                (Choice
                                   (ChoiceId "1" "carol") [
                                   (Bound 1 1)]) Close)
                             ,
                             (Case
                                (Choice
                                   (ChoiceId "1" "carol") [
                                   (Bound 0 0)])
                                (Pay
                                   (AccountId 0 "alice")
                                   (Party "bob")
                                   (Constant 450) Close))] 100 Close)))] 60
                 (When [
                       (Case
                          (Choice
                             (ChoiceId "1" "carol") [
                             (Bound 1 1)]) Close)
                       ,
                       (Case
                          (Choice
                             (ChoiceId "1" "carol") [
                             (Bound 0 0)])
                          (Pay
                             (AccountId 0 "alice")
                             (Party "bob")
                             (Constant 450) Close))] 100 Close)))
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
                             (Constant 450) Close) Close)
                       (When [
                             (Case
                                (Choice
                                   (ChoiceId "1" "carol") [
                                   (Bound 1 1)]) Close)
                             ,
                             (Case
                                (Choice
                                   (ChoiceId "1" "carol") [
                                   (Bound 0 0)])
                                (Pay
                                   (AccountId 0 "alice")
                                   (Party "bob")
                                   (Constant 450) Close))] 100 Close)))] 60
                 (When [
                       (Case
                          (Choice
                             (ChoiceId "1" "carol") [
                             (Bound 1 1)]) Close)
                       ,
                       (Case
                          (Choice
                             (ChoiceId "1" "carol") [
                             (Bound 0 0)])
                          (Pay
                             (AccountId 0 "alice")
                             (Party "bob")
                             (Constant 450) Close))] 100 Close)))] 40 Close))] 10 Close"""

-- These parsers are not used by the front end at this time and so they are `Parser String (Identity a)`
-- rather than `Parser String (Term a)`
input :: Parser String S.Input
input =
  maybeParens
    ( (S.IDeposit <$> (string "IDeposit" **> accountIdValue) <**> parseToValue party <**> parseToValue token <**> (maybeParens bigInteger))
        <|> (S.IChoice <$> (string "IChoice" **> choiceIdValue) <**> (maybeParens bigInteger))
        <|> ((const S.INotify) <$> (string "INotify"))
    )

accountIdValue :: Parser String S.AccountId
accountIdValue = parseToValue accountId

choiceIdValue :: Parser String S.ChoiceId
choiceIdValue = parseToValue choiceId

valueIdValue :: Parser String S.ValueId
valueIdValue = parseToValue valueId

payeeValue :: Parser String S.Payee
payeeValue = parseToValue payee

inputList :: Parser String (List S.Input)
inputList = haskellList input

slotInterval :: Parser String SlotInterval
slotInterval =
  parens do
    void maybeSpaces
    minSlot <- slot
    void maybeSpaces
    void $ string ","
    void maybeSpaces
    maxSlot <- slot
    void maybeSpaces
    pure $ SlotInterval minSlot maxSlot

transactionInput :: Parser String TransactionInput
transactionInput = do
  void $ string "TransactionInput"
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
transactionWarning = do
  void maybeSpaces
  tWa <-
    maybeParens
      ( do
          void maybeSpaces
          tWaS <-
            (TransactionNonPositiveDeposit <$> (string "TransactionNonPositiveDeposit" **> parseToValue party) <**> accountIdValue <**> parseToValue token <**> maybeParens bigInteger)
              <|> (TransactionNonPositivePay <$> (string "TransactionNonPositivePay" **> accountIdValue) <**> (parens payeeValue) <**> parseToValue token <**> maybeParens bigInteger)
              <|> (TransactionPartialPay <$> (string "TransactionPartialPay" **> accountIdValue) <**> (parens payeeValue) <**> parseToValue token <**> maybeParens bigInteger <**> maybeParens bigInteger)
              <|> (TransactionShadowing <$> (string "TransactionShadowing" **> valueIdValue) <**> (maybeParens bigInteger) <**> (maybeParens bigInteger))
          void maybeSpaces
          pure tWaS
      )
  void maybeSpaces
  pure tWa

transactionWarningList :: Parser String (List TransactionWarning)
transactionWarningList = haskellList transactionWarning

testTransactionWarningParsing :: String
testTransactionWarningParsing = "[TransactionNonPositivePay (AccountId 1 \"Bob\") (Party \"Bob\") (-10),TransactionPartialPay (AccountId 1 \"Bob\") (Party \"Alice\") 0 21]"
