module Marlowe.Parser where

import Control.Alternative ((<|>))
import Control.Lazy (fix)
import Control.Monad.State as MonadState
import Data.Array (foldMap, fromFoldable, many, (:))
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Either (Either)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Eq (genericEq)
import Data.Generic.Rep.Show (genericShow)
import Data.Identity (Identity)
import Data.List (List, some)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits (fromCharArray)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Marlowe.Pretty (class Pretty, prettyFragment)
import Marlowe.Semantics (AccountIdF(..), ActionF(..), Ada(..), BoundF(..), CaseF(..), ChoiceIdF(..), ContractF(..), IdentityF(..), InputF(..), ObservationF(..), Party, PayeeF(..), PubKey, Slot(..), SlotInterval(..), Timeout, TransactionInput, TransactionInputF(..), TransactionWarning(..), ValueF(..), ValueIdF(..))
import Marlowe.Semantics as Semantics
import Prelude (class Eq, class Monoid, class Semigroup, class Show, append, bind, const, discard, flip, mempty, pure, show, void, ($), (*>), (<$>), (<*), (<*>), (<<<), (<>))
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

data MarloweType
  = StringType
  | BigIntegerType
  | SlotType
  | AccountIdType
  | ChoiceIdType
  | ValueIdType
  | ActionType
  | PayeeType
  | CaseType
  | ValueType
  | InputType
  | ObservationType
  | ContractType

derive instance genericMarloweType :: Generic MarloweType _

instance showMarloweType :: Show MarloweType where
  show = genericShow

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

-- a concrete type for holes only
data MarloweHole
  = MarloweHole
    { name :: String
    , marloweType :: MarloweType
    , start :: Position
    , end :: Position
    }

class IsMarloweType a where
  marloweType :: Proxy a -> MarloweType

instance stringIsMarloweType :: IsMarloweType String where
  marloweType _ = StringType

instance bigIntegerIsMarloweType :: IsMarloweType BigInteger where
  marloweType _ = BigIntegerType

-- a Monoid for collecting Holes
data Holes
  = Holes (Map String (Array MarloweHole))

instance semigroupHoles :: Semigroup Holes where
  append (Holes a) (Holes b) = Holes (Map.unionWith append a b)

instance monoidHoles :: Monoid Holes where
  mempty = Holes mempty

{- | Find holes with the same name
  We collect all the `Holes` using `getHoles` and then we fold through the result
  to find occurances that have the same name as well as changing the values to be
  single MarloweHoles rather than an array of MarloweHoles
-}
validateHoles :: Holes -> Tuple (Array MarloweHole) (Map String MarloweHole)
validateHoles (Holes m) = foldlWithIndex f (Tuple [] mempty) m
  where
  f k (Tuple duplicates uniquesMap) [ v ] = Tuple duplicates (Map.insert k v uniquesMap)

  f k (Tuple duplicates uniquesMap) vs = Tuple (duplicates <> vs) uniquesMap

insertHole :: forall a. IsMarloweType a => Holes -> Term a -> Holes
insertHole m (Term _) = m

insertHole (Holes m) (Hole name proxy start end) = Holes $ Map.alter f name m
  where
  marloweHole = MarloweHole { name, marloweType: (marloweType proxy), start, end }

  f (Just v) = Just (marloweHole : v)

  f Nothing = Just [ marloweHole ]

class HasMarloweHoles a where
  getHoles :: Holes -> a -> Holes

instance arrayHasMarloweHoles :: HasMarloweHoles a => HasMarloweHoles (Array a) where
  getHoles m as = foldMap (getHoles m) as

-- Parsable versions of the Marlowe types
type Bound
  = BoundF Term

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

instance boundHasMarloweHoles :: HasMarloweHoles (BoundF Term) where
  getHoles m (Bound a b) = insertHole m a <> insertHole m b

instance boundFromTerm :: FromTerm BoundF where
  fromTerm (Bound a b) = Bound <$> termToValue a <*> termToValue b

instance slotMarloweType :: IsMarloweType Slot where
  marloweType _ = SlotType

instance payeeFromTerm :: FromTerm PayeeF where
  fromTerm (Account a) = Account <$> fromTerm a
  fromTerm (Party (Term a)) = pure $ Party $ Identity a
  fromTerm _ = Nothing

instance payeeMarloweType :: IsMarloweType (PayeeF f) where
  marloweType _ = PayeeType

instance payeeHasMarloweHoles :: HasMarloweHoles (PayeeF Term) where
  getHoles m (Account a) = getHoles m a
  getHoles m (Party a) = insertHole m a

instance actionFromTerm :: FromTerm ActionF where
  fromTerm (Deposit a b c) = Deposit <$> fromTerm a <*> termToValue b <*> fromTerm c
  fromTerm (Choice a b) = Choice <$> fromTerm a <*> (traverse fromTerm b)
  fromTerm (Notify a) = Notify <$> fromTerm a

instance actionMarloweType :: IsMarloweType (ActionF f) where
  marloweType _ = ActionType

instance actionHasMarloweHoles :: HasMarloweHoles (ActionF Term) where
  getHoles m (Deposit a b c) = getHoles m a <> insertHole m b <> getHoles m c
  getHoles m (Choice a b) = getHoles m a <> getHoles m b
  getHoles m (Notify a) = getHoles m a

instance caseFromTerm :: FromTerm CaseF where
  fromTerm (Case a b) = Case <$> fromTerm a <*> fromTerm b

instance caseMarloweType :: IsMarloweType (CaseF f) where
  marloweType _ = CaseType

instance caseHasMarloweHoles :: HasMarloweHoles (CaseF Term) where
  getHoles m (Case a b) = getHoles m a <> getHoles m b

instance accountIdFromTerm :: FromTerm AccountIdF where
  fromTerm (AccountId (Term b) (Term c)) = pure $ AccountId (Identity b) (Identity c)
  fromTerm _ = Nothing

instance accountIdIsMarloweType :: IsMarloweType (AccountIdF Term) where
  marloweType _ = AccountIdType

instance accountIdHasMarloweHoles :: HasMarloweHoles (AccountIdF Term) where
  getHoles m (AccountId a b) = insertHole m a <> insertHole m b

instance choiceIdFromTerm :: FromTerm ChoiceIdF where
  fromTerm (ChoiceId (Term a) (Term b)) = pure $ ChoiceId (Identity a) (Identity b)
  fromTerm _ = Nothing

instance choiceIdIsMarloweType :: IsMarloweType (ChoiceIdF Term) where
  marloweType _ = ChoiceIdType

instance choiceIdHasMarloweHoles :: HasMarloweHoles (ChoiceIdF Term) where
  getHoles m (ChoiceId a b) = insertHole m a <> insertHole m b

instance valueIdFromTerm :: FromTerm ValueIdF where
  fromTerm (ValueId (Term a)) = pure $ ValueId (Identity a)
  fromTerm _ = Nothing

instance valueIdIsMarloweType :: IsMarloweType (ValueIdF Term) where
  marloweType _ = ValueIdType

instance valueIdHasMarloweHoles :: HasMarloweHoles (ValueIdF Term) where
  getHoles m (ValueId a) = insertHole m a

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

instance valueIsMarloweType :: IsMarloweType (ValueF Term) where
  marloweType _ = ValueType

instance valueHasMarloweHoles :: HasMarloweHoles (ValueF Term) where
  getHoles m (AvailableMoney a) = getHoles m a
  getHoles m (Constant a) = insertHole m a
  getHoles m (NegValue a) = getHoles m a
  getHoles m (AddValue a b) = getHoles m a <> getHoles m b
  getHoles m (SubValue a b) = getHoles m a <> getHoles m b
  getHoles m (ChoiceValue a b) = getHoles m a <> getHoles m b
  getHoles m SlotIntervalStart = mempty
  getHoles m SlotIntervalEnd = mempty
  getHoles m (UseValue a) = getHoles m a

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

instance observationIsMarloweType :: IsMarloweType (ObservationF Term) where
  marloweType _ = ObservationType

instance observationHasMarloweHoles :: HasMarloweHoles (ObservationF Term) where
  getHoles m (AndObs a b) = getHoles m a <> getHoles m b
  getHoles m (OrObs a b) = getHoles m a <> getHoles m b
  getHoles m (NotObs a) = getHoles m a
  getHoles m (ChoseSomething a) = getHoles m a
  getHoles m (ValueGE a b) = getHoles m a <> getHoles m b
  getHoles m (ValueGT a b) = getHoles m a <> getHoles m b
  getHoles m (ValueLT a b) = getHoles m a <> getHoles m b
  getHoles m (ValueLE a b) = getHoles m a <> getHoles m b
  getHoles m (ValueEQ a b) = getHoles m a <> getHoles m b
  getHoles m TrueObs = mempty
  getHoles m FalseObs = mempty

instance contractFromTerm :: FromTerm ContractF where
  fromTerm Close = pure Semantics.Close
  fromTerm (Pay a b c d) = Pay <$> fromTerm a <*> fromTerm b <*> fromTerm c <*> fromTerm d
  fromTerm (If a b c) = If <$> fromTerm a <*> fromTerm b <*> fromTerm c
  fromTerm (When as b c) = When <$> (traverse fromTerm as) <*> termToValue b <*> fromTerm c
  fromTerm (Let a b c) = Let <$> fromTerm a <*> fromTerm b <*> fromTerm c

instance contractIsMarloweType :: IsMarloweType (ContractF Term) where
  marloweType _ = ContractType

instance contractHasMarloweHoles :: HasMarloweHoles (ContractF Term) where
  getHoles m Close = mempty
  getHoles m (Pay a b c d) = getHoles m a <> getHoles m b <> getHoles m c <> getHoles m d
  getHoles m (If a b c) = getHoles m a <> getHoles m b <> getHoles m c
  getHoles m (When a b c) = getHoles m a <> insertHole m b <> getHoles m c
  getHoles m (Let a b c) = getHoles m a <> getHoles m b <> getHoles m c

hole :: forall a. Parser String (Term a)
hole = do
  (ParseState _ start _) <- MonadState.get
  name <- fromCharArray <$> (char '?' *> many alphaNum)
  (ParseState _ end _) <- MonadState.get
  pure $ Hole name Proxy start end

parseTerm :: forall a. Parser String a -> Parser String (Term a)
parseTerm p = hole <|> (Term <$> p)

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
    <|> (Constant <$> (string "Constant" **> bigIntegerTerm))
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
    <|> (Party <$> (string "Party" **> parseTerm text))

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
    first <- parseTerm $ maybeParens bigInteger
    void spaces
    second <- parseTerm $ maybeParens bigInteger
    void maybeSpaces
    pure (Bound first second)

action :: Parser String Action
action =
  (Deposit <$> (string "Deposit" **> accountId) <**> parseTerm party <**> value')
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
    <|> (When <$> (string "When" **> (array (maybeParens case'))) <**> parseTerm timeout <**> contract')
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
    (Party (Term p)) -> pure $ Party (Identity p)
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
