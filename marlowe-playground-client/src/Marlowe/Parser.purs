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
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Eq (genericEq)
import Data.Identity (Identity)
import Data.List (List, some)
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits (fromCharArray)
import Data.Traversable (traverse)
import Marlowe.Pretty (class Pretty, prettyFragment)
import Marlowe.Semantics (AccountIdF(..), ActionF(..), Ada(..), Bound(..), CaseF(..), ChoiceIdF(..), ContractF(..), IdentityF(..), InputF(..), ObservationF(..), Party, PayeeF(..), PubKey, Slot(..), SlotInterval(..), Timeout, TransactionInput, TransactionInputF(..), TransactionWarning(..), ValueF(..), ValueIdF(..))
import Marlowe.Semantics as Semantics
import Prelude (class Eq, class Show, bind, const, discard, flip, pure, show, void, ($), (*>), (<$>), (<*), (<*>), (<<<), (<>))
import Text.Parsing.Parser (ParseState(..), Parser, ParserT, fail, runParser)
import Text.Parsing.Parser.Basic (integral, parens)
import Text.Parsing.Parser.Combinators (between, choice, sepBy)
import Text.Parsing.Parser.Pos (Position)
import Text.Parsing.Parser.String (char, string)
import Text.Parsing.Parser.Token (alphaNum, space)
import Text.PrettyPrint.Leijen as Leijen
import Type.Proxy (Proxy(..))

parse :: forall a. Parser String a -> String -> Either String a
parse p = lmap show <<< flip runParser (parens p <|> p)

data Term a
  = Term a
  | Hole String (Proxy a) Position Position

derive instance genericTerm :: Generic (Term a) _

instance eqTerm :: Eq a => Eq (Term a) where
  eq a b = genericEq a b

instance showTerm :: Show a => Show (Term a) where
  show (Term a) = show a
  show (Hole name _ _ _) = "?" <> name

instance prettyTerm :: Pretty a => Pretty (Term a) where
  prettyFragment (Term a) = prettyFragment a
  prettyFragment (Hole name _ _ _) = Leijen.text $ "?" <> name

hole :: forall a. Parser String (Term a)
hole = do
  (ParseState _ start _) <- MonadState.get
  name <- fromCharArray <$> (char '?' *> many alphaNum)
  (ParseState _ end _) <- MonadState.get
  pure $ Hole name Proxy start end

parseTerm :: forall a. Parser String a -> Parser String (Term a)
parseTerm p = hole <|> (Term <$> p)

-- Parsable versions of the Marlowe types
type AccountId
  = AccountIdF Term

type ChoiceId
  = ChoiceIdF Term

type ValueId
  = ValueIdF Term

type Action
  = ActionF Term

type Payee
  = PayeeF Term

type Case
  = CaseF Term

type Value
  = ValueF Term

type Input
  = InputF Term

type Observation
  = ObservationF Term

type Contract
  = ContractF Term

termToValue :: forall a. Term a -> Maybe (IdentityF a)
termToValue (Term a) = Just (Identity a)

termToValue _ = Nothing

class FromTerm f where
  fromTerm :: f Term -> Maybe (f IdentityF)

instance payeeFromTerm :: FromTerm PayeeF where
  fromTerm (Account a) = Account <$> fromTerm a
  fromTerm (Party b) = pure $ Party b

instance actionFromTerm :: FromTerm ActionF where
  fromTerm (Deposit a b c) = Deposit <$> fromTerm a <*> pure b <*> fromTerm c
  fromTerm (Choice a b) = Choice <$> fromTerm a <*> pure b
  fromTerm (Notify a) = Notify <$> fromTerm a

instance caseFromTerm :: FromTerm CaseF where
  fromTerm (Case a b) = Case <$> fromTerm a <*> fromTerm b

instance accountIdFromTerm :: FromTerm AccountIdF where
  fromTerm (AccountId (Term b) (Term c)) = pure $ AccountId (Identity b) (Identity c)
  fromTerm _ = Nothing

instance choiceIdFromTerm :: FromTerm ChoiceIdF where
  fromTerm (ChoiceId (Term a) (Term b)) = pure $ ChoiceId (Identity a) (Identity b)
  fromTerm _ = Nothing

instance valueIdFromTerm :: FromTerm ValueIdF where
  fromTerm (ValueId (Term a)) = pure $ ValueId (Identity a)
  fromTerm _ = Nothing

instance valueFromTerm :: FromTerm ValueF where
  fromTerm (AvailableMoney accountIdF) = AvailableMoney <$> fromTerm accountIdF
  fromTerm (Constant a) = Constant <$> termToValue a
  fromTerm (NegValue a) = NegValue <$> fromTerm a
  fromTerm (AddValue a b) = AddValue <$> fromTerm a <*> fromTerm b
  fromTerm (SubValue a b) = SubValue <$> fromTerm a <*> fromTerm b
  fromTerm (ChoiceValue a b) = ChoiceValue <$> fromTerm a <*> fromTerm b
  fromTerm SlotIntervalStart = pure SlotIntervalStart
  fromTerm SlotIntervalEnd = pure SlotIntervalEnd
  fromTerm (UseValue a) = UseValue <$> fromTerm a

instance observationFromTerm :: FromTerm ObservationF where
  fromTerm (AndObs a b) = AndObs <$> fromTerm a <*> fromTerm b
  fromTerm (OrObs a b) = OrObs <$> fromTerm a <*> fromTerm b
  fromTerm (NotObs a) = NotObs <$> fromTerm a
  fromTerm (ChoseSomething a) = ChoseSomething <$> fromTerm a
  fromTerm (ValueGE a b) = ValueGE <$> fromTerm a <*> fromTerm b
  fromTerm (ValueGT a b) = ValueGT <$> fromTerm a <*> fromTerm b
  fromTerm (ValueLT a b) = ValueLT <$> fromTerm a <*> fromTerm b
  fromTerm (ValueLE a b) = ValueLE <$> fromTerm a <*> fromTerm b
  fromTerm (ValueEQ a b) = ValueEQ <$> fromTerm a <*> fromTerm b
  fromTerm TrueObs = pure TrueObs
  fromTerm FalseObs = pure FalseObs

instance contractFromTerm :: FromTerm ContractF where
  fromTerm Close = pure Semantics.Close
  fromTerm (Pay a b c d) = Pay <$> fromTerm a <*> fromTerm b <*> fromTerm c <*> fromTerm d
  fromTerm (If a b c) = If <$> fromTerm a <*> fromTerm b <*> fromTerm c
  fromTerm (When as b c) = When <$> (traverse fromTerm as) <*> pure b <*> fromTerm c
  fromTerm (Let a b c) = Let <$> fromTerm a <*> fromTerm b <*> fromTerm c

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
text = between (char '"') (char '"') $ fromCharArray <<< fromFoldable <$> many (choice [ alphaNum, space ])

haskellList :: forall a. Parser String a -> Parser String (List a)
haskellList p =
  squareParens
    $ do
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

bigIntegerTerm :: Parser String (Term BigInteger)
bigIntegerTerm = parseTerm bigInteger

valueId :: Parser String ValueId
valueId = ValueId <$> parseTerm text

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
    second <- parseTerm text
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
    second <- parseTerm text
    void maybeSpaces
    pure $ ChoiceId first second

atomValue :: Parser String Value
atomValue =
  (pure SlotIntervalStart <* string "SlotIntervalStart")
    <|> (pure SlotIntervalEnd <* string "SlotIntervalEnd")

recValue :: Parser String Value
recValue =
  (AvailableMoney <$> (string "AvailableMoney" **> accountId))
    <|> (Constant <$> (string "Constant" **> parseTerm (maybeParens bigInteger)))
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
  (pure TrueObs <* string "TrueObs")
    <|> (pure FalseObs <* string "FalseObs")

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
payee =
  (Account <$> (string "Account" **> accountId))
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
  pure $ Case first second
  where
  contract' = atomContract <|> fix \p -> parens recContract

cases :: Parser String (Array Case)
cases = array case'

atomContract :: Parser String Contract
atomContract = pure Close <* string "Close"

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

contractTerm :: Parser String Contract
contractTerm = do
  void maybeSpaces
  c <- (atomContract <|> recContract)
  void maybeSpaces
  pure c

contract :: Parser String Semantics.Contract
contract = do
  c <- contractTerm
  case fromTerm c of
    Just contract' -> pure contract'
    Nothing -> fail "Contract has holes"

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
input :: Parser String (InputF IdentityF)
input =
  (IDeposit <$> (string "IDeposit" **> accountIdValue) <**> party <**> (Lovelace <$> (maybeParens bigInteger)))
    <|> (IChoice <$> (string "IChoice" **> choiceIdValue) <**> (maybeParens bigInteger))
    <|> ((const INotify) <$> (string "INotify"))

accountIdValue :: ParserT String Identity (AccountIdF IdentityF)
accountIdValue = do
  accountId' <- accountId
  case accountId' of
    (AccountId (Term a) (Term b)) -> pure $ AccountId (Identity a) (Identity b)
    _ -> fail "Found a hole when parsing an AccountIf"

choiceIdValue :: ParserT String Identity (ChoiceIdF IdentityF)
choiceIdValue = do
  choiceId' <- choiceId
  case choiceId' of
    (ChoiceId (Term a) (Term b)) -> pure $ ChoiceId (Identity a) (Identity b)
    _ -> fail "Found a hole when parsing an ChoiceId"

valueIdValue :: ParserT String Identity (ValueIdF IdentityF)
valueIdValue = do
  valueId' <- valueId
  case valueId' of
    (ValueId (Term a)) -> pure $ ValueId (Identity a)
    _ -> fail "Found a hole when parsing an ValueId"

payeeValue :: ParserT String Identity (PayeeF IdentityF)
payeeValue = do
  payee' <- payee
  case payee' of
    (Account (AccountId (Term a) (Term b))) -> pure $ Account (AccountId (Identity a) (Identity b))
    (Party p) -> pure $ Party p
    _ -> fail "Found a hole when parsing an Payee"

inputList :: Parser String (List (InputF IdentityF))
inputList = haskellList input

slotInterval :: Parser String SlotInterval
slotInterval = (SlotInterval <$> (string "SlotInterval" **> slot) <**> slot)

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
transactionWarning =
  (TransactionNonPositiveDeposit <$> (string "TransactionNonPositiveDeposit" **> party) <**> accountIdValue <**> (Lovelace <$> (maybeParens bigInteger)))
    <|> (TransactionNonPositivePay <$> (string "TransactionNonPositivePay" **> accountIdValue) <**> (parens payeeValue) <**> (Lovelace <$> (maybeParens bigInteger)))
    <|> (TransactionPartialPay <$> (string "TransactionPartialPay" **> accountIdValue) <**> (parens payeeValue) <**> (Lovelace <$> (maybeParens bigInteger)) <**> (Lovelace <$> (maybeParens bigInteger)))
    <|> (TransactionShadowing <$> (string "TransactionShadowing" **> valueIdValue) <**> (maybeParens bigInteger) <**> (maybeParens bigInteger))

transactionWarningList :: Parser String (List TransactionWarning)
transactionWarningList = haskellList transactionWarning

testTransactionWarningParsing :: String
testTransactionWarningParsing = "[TransactionNonPositivePay (AccountId 1 \"Bob\") (Party \"Bob\") (-10),TransactionPartialPay (AccountId 1 \"Bob\") (Party \"Alice\") 0 21]"
