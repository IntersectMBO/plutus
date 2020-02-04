module Marlowe.Parser where

import Control.Alternative ((<|>))
import Control.Lazy (fix)
import Data.Array (fromFoldable, many)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Either (Either)
import Data.List (List)
import Data.Maybe (Maybe(..))
import Data.String (length)
import Data.String.CodeUnits (fromCharArray)
import Marlowe.Holes (class FromTerm, AccountId(..), Action(..), Bound(..), Case(..), ChoiceId(..), Contract(..), Observation(..), Party(..), Payee(..), Term(..), Token(..), Value(..), ValueId(..), fromTerm)
import Marlowe.Semantics (CurrencySymbol, PubKey, Slot(..), SlotInterval(..), Timeout, TransactionInput(..), TransactionWarning(..), TokenName)
import Marlowe.Semantics as S
import Prelude (bind, const, discard, pure, show, void, ($), (*>), (-), (<$>), (<*), (<*>), (<<<))
import Text.Parsing.StringParser (Parser(..), fail, runParser)
import Text.Parsing.StringParser.Basic (integral, parens, someWhiteSpace, whiteSpaceChar)
import Text.Parsing.StringParser.CodeUnits (alphaNum, char, skipSpaces, string)
import Text.Parsing.StringParser.Combinators (between, choice, sepBy)
import Type.Proxy (Proxy(..))

parse :: forall a. Parser a -> String -> Either String a
parse p = lmap show <<< runParser (parens p <|> p)

parseToValue :: forall a b. FromTerm a b => Parser a -> Parser b
parseToValue p = do
  v <- p
  let
    mV = fromTerm v
  case mV of
    (Just a) -> pure a
    _ -> fail "Found a hole but was expecting terms only"

hole :: forall a. Parser (Term a)
hole =
  Parser \s -> do
    let
      (Parser p) = fromCharArray <$> (char '?' *> many nameChars)
    { result: name, suffix } <- p s
    let
      start = suffix.pos - (length name) - 1

      end = suffix.pos
    pure { result: Hole name Proxy start end, suffix }
  where
  nameChars = alphaNum <|> char '_'

parseTerm :: forall a. Parser a -> Parser (Term a)
parseTerm p = hole <|> (Term <$> p)

-- All arguments are space separated so we add **> to reduce boilerplate
appRSpaces :: forall a b. Parser a -> Parser b -> Parser b
appRSpaces p q = p *> someWhiteSpace *> q

infixl 4 appRSpaces as **>

appSpaces :: forall a b. Parser (a -> b) -> Parser a -> Parser b
appSpaces p q = p <*> (someWhiteSpace *> q)

infixl 4 appSpaces as <**>

text :: Parser String
text = between (char '"') (char '"') $ fromCharArray <<< fromFoldable <$> many (choice [ alphaNum, whiteSpaceChar ])

squareParens :: forall a. Parser a -> Parser a
squareParens = between (string "[") (string "]")

haskellList :: forall a. Parser a -> Parser (List a)
haskellList p = squareParens (trim p `sepBy` string ",")

trim :: forall a. Parser a -> Parser a
trim p = do
  skipSpaces
  v <- p
  skipSpaces
  pure v

maybeParens :: forall a. Parser a -> Parser a
maybeParens p = parens p <|> p

array :: forall a. Parser a -> Parser (Array a)
array p = Array.fromFoldable <$> haskellList p

----------------------------------------------------------------------
bigInteger :: Parser BigInteger
bigInteger = do
  i <- integral
  case BigInteger.fromString i of
    (Just v) -> pure v
    Nothing -> fail "not a valid BigInt"

bigIntegerTerm :: Parser (Term BigInteger)
bigIntegerTerm = parseTerm bigInteger

valueId :: Parser ValueId
valueId = ValueId <$> text

slot :: Parser Slot
slot = Slot <$> maybeParens bigInteger

slotTerm :: Parser (Term Slot)
slotTerm = parseTerm slot

timeout :: Parser Timeout
timeout = slot

accountId :: Parser AccountId
accountId =
  parens do
    skipSpaces
    void $ string "AccountId"
    void someWhiteSpace
    first <- parseTerm $ maybeParens bigInteger
    void someWhiteSpace
    second <- parseTerm $ parens party
    skipSpaces
    pure $ AccountId first second

choiceId :: Parser ChoiceId
choiceId =
  parens do
    skipSpaces
    void $ string "ChoiceId"
    void someWhiteSpace
    first <- parseTerm text
    void someWhiteSpace
    second <- parseTerm $ parens party
    skipSpaces
    pure $ ChoiceId first second

atomValue :: Parser Value
atomValue =
  (pure SlotIntervalStart <* string "SlotIntervalStart")
    <|> (pure SlotIntervalEnd <* string "SlotIntervalEnd")

recValue :: Parser Value
recValue =
  (AvailableMoney <$> (string "AvailableMoney" **> parseTerm accountId) <**> parseTerm (parens token))
    <|> (Constant <$> (string "Constant" **> bigIntegerTerm))
    <|> (NegValue <$> (string "NegValue" **> value'))
    <|> (AddValue <$> (string "AddValue" **> value') <**> value')
    <|> (SubValue <$> (string "SubValue" **> value') <**> value')
    <|> (ChoiceValue <$> (string "ChoiceValue" **> parseTerm choiceId) <**> value')
    <|> (UseValue <$> (string "UseValue" **> parseTerm valueId))
  where
  value' = parseTerm $ atomValue <|> fix (\p -> parens recValue)

value :: Parser Value
value = atomValue <|> recValue

atomObservation :: Parser Observation
atomObservation =
  (pure TrueObs <* string "TrueObs")
    <|> (pure FalseObs <* string "FalseObs")

recObservation :: Parser Observation
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

observation :: Parser Observation
observation = atomObservation <|> recObservation

payee :: Parser Payee
payee =
  (Account <$> (string "Account" **> parseTerm accountId))
    <|> (Party <$> (string "Party" **> parseTerm (parens party)))

pubkey :: Parser PubKey
pubkey = text

party :: Parser Party
party =
  (PK <$> (string "PK" **> parseTerm pubkey))
    <|> (Role <$> (string "Role" **> parseTerm tokenName))

currencySymbol :: Parser CurrencySymbol
currencySymbol = text

tokenName :: Parser TokenName
tokenName = text

token :: Parser Token
token = do
  skipSpaces
  void $ string "Token"
  void someWhiteSpace
  first <- parseTerm text
  void someWhiteSpace
  second <- parseTerm text
  skipSpaces
  pure $ Token first second

bound :: Parser Bound
bound = do
  skipSpaces
  void $ string "Bound"
  void someWhiteSpace
  first <- parseTerm $ maybeParens bigInteger
  void someWhiteSpace
  second <- parseTerm $ maybeParens bigInteger
  skipSpaces
  pure (Bound first second)

action :: Parser Action
action =
  (Deposit <$> (string "Deposit" **> parseTerm accountId) <**> parseTerm (parens party) <**> parseTerm (parens token) <**> value')
    <|> (Choice <$> (string "Choice" **> parseTerm choiceId) <**> array (maybeParens (parseTerm bound)))
    <|> (Notify <$> (string "Notify" **> observation'))
  where
  observation' = parseTerm $ atomObservation <|> fix \p -> parens recObservation

  value' = parseTerm $ atomValue <|> fix (\p -> parens recValue)

case' :: Parser Case
case' = do
  void $ string "Case"
  void someWhiteSpace
  first <- parseTerm $ parens action
  void someWhiteSpace
  second <- parseTerm contract'
  pure $ Case first second
  where
  contract' = atomContract <|> fix \p -> parens recContract

cases :: Parser (Array Case)
cases = array case'

atomContract :: Parser Contract
atomContract = pure Close <* string "Close"

recContract :: Parser Contract
recContract =
  ( Pay <$> (string "Pay" **> parseTerm accountId)
      <**> parseTerm (parens payee)
      <**> parseTerm (parens token)
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

contract :: Parser Contract
contract = do
  skipSpaces
  c <- (atomContract <|> recContract)
  skipSpaces
  pure c

contractValue :: Parser S.Contract
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

input :: Parser S.Input
input =
  maybeParens
    ( (S.IDeposit <$> (string "IDeposit" **> accountIdValue) <**> parseToValue (parens party) <**> parseToValue (parens token) <**> (maybeParens bigInteger))
        <|> (S.IChoice <$> (string "IChoice" **> choiceIdValue) <**> (maybeParens bigInteger))
        <|> ((const S.INotify) <$> (string "INotify"))
    )

accountIdValue :: Parser S.AccountId
accountIdValue = parseToValue accountId

choiceIdValue :: Parser S.ChoiceId
choiceIdValue = parseToValue choiceId

valueIdValue :: Parser S.ValueId
valueIdValue = parseToValue valueId

payeeValue :: Parser S.Payee
payeeValue = parseToValue payee

inputList :: Parser (List S.Input)
inputList = haskellList input

slotInterval :: Parser SlotInterval
slotInterval =
  parens do
    skipSpaces
    minSlot <- slot
    skipSpaces
    void $ string ","
    skipSpaces
    maxSlot <- slot
    skipSpaces
    pure $ SlotInterval minSlot maxSlot

transactionInput :: Parser TransactionInput
transactionInput = do
  void $ string "TransactionInput"
  skipSpaces
  void $ string "{"
  skipSpaces
  void $ string "txInterval"
  skipSpaces
  void $ string "="
  skipSpaces
  interval <- slotInterval
  skipSpaces
  void $ string ","
  skipSpaces
  void $ string "txInputs"
  skipSpaces
  void $ string "="
  skipSpaces
  inputs <- inputList
  skipSpaces
  void $ string "}"
  pure $ TransactionInput { interval, inputs }

transactionInputList :: Parser (List TransactionInput)
transactionInputList = haskellList transactionInput

testTransactionInputParsing :: String
testTransactionInputParsing = "[TransactionInput { txInterval = (2 , 8), txInputs = [ (IDeposit (AccountId 0 (Role \"investor\")) (Role \"investor\") (Token \"\" \"\") 850)]}]"

transactionWarning :: Parser TransactionWarning
transactionWarning = do
  skipSpaces
  tWa <-
    maybeParens
      ( do
          skipSpaces
          tWaS <-
            (TransactionNonPositiveDeposit <$> (string "TransactionNonPositiveDeposit" **> parseToValue (parens party)) <**> accountIdValue <**> parseToValue (parens token) <**> maybeParens bigInteger)
              <|> (TransactionNonPositivePay <$> (string "TransactionNonPositivePay" **> accountIdValue) <**> (parens payeeValue) <**> parseToValue (parens token) <**> maybeParens bigInteger)
              <|> (TransactionPartialPay <$> (string "TransactionPartialPay" **> accountIdValue) <**> (parens payeeValue) <**> parseToValue (parens token) <**> maybeParens bigInteger <**> maybeParens bigInteger)
              <|> (TransactionShadowing <$> (string "TransactionShadowing" **> valueIdValue) <**> (maybeParens bigInteger) <**> (maybeParens bigInteger))
          skipSpaces
          pure tWaS
      )
  skipSpaces
  pure tWa

transactionWarningList :: Parser (List TransactionWarning)
transactionWarningList = haskellList transactionWarning

testTransactionWarningParsing :: String
testTransactionWarningParsing =
  """[
  (TransactionPartialPay
    (AccountId 0
      (Role "investor"))
    (Party
      (Role "investor"))
    (Token "" "") 1000 1300)]"""
