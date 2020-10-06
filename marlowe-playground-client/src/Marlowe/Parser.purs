module Marlowe.Parser where

import Control.Alternative ((<|>))
import Control.Lazy (fix)
import Data.Array (fromFoldable, many)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Either (Either(..))
import Data.Function.Uncurried (Fn5, runFn5)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.List (List)
import Data.Maybe (Maybe(..))
import Data.String (length)
import Data.String.CodeUnits (fromCharArray)
import Data.Unit (Unit, unit)
import Marlowe.Holes (class FromTerm, AccountId, Action(..), Bound(..), Case(..), ChoiceId(..), Contract(..), Observation(..), Party(..), Payee(..), Range, Term(..), TermWrapper(..), Token(..), Value(..), ValueId(..), fromTerm, getRange, mkHole)
import Marlowe.Semantics (CurrencySymbol, Rational(..), PubKey, Slot(..), SlotInterval(..), TransactionInput(..), TransactionWarning(..), TokenName)
import Marlowe.Semantics as S
import Prelude (class Show, bind, const, discard, pure, show, void, zero, ($), (*>), (-), (<$), (<$>), (<*), (<*>), (<<<))
import Text.Parsing.StringParser (Parser(..), fail, runParser)
import Text.Parsing.StringParser.Basic (integral, parens, someWhiteSpace, whiteSpaceChar)
import Text.Parsing.StringParser.CodeUnits (alphaNum, char, skipSpaces, string)
import Text.Parsing.StringParser.Combinators (between, choice, sepBy)
import Type.Proxy (Proxy(..))

type HelperFunctions a
  = { mkHole :: String -> Range -> Term a
    , mkTerm :: a -> Range -> Term a
    , mkTermWrapper :: a -> Range -> TermWrapper a
    , getRange :: Term a -> Range
    , mkBigInteger :: Int -> BigInteger
    , mkTimeout :: Int -> Range -> TermWrapper Slot
    , mkClose :: Contract
    , mkPay :: AccountId -> Term Payee -> Term Token -> Term Value -> Term Contract -> Contract
    , mkWhen :: Array (Term Case) -> (TermWrapper Slot) -> Term Contract -> Contract
    , mkIf :: Term Observation -> Term Contract -> Term Contract -> Contract
    , mkLet :: TermWrapper ValueId -> Term Value -> Term Contract -> Contract
    , mkAssert :: Term Observation -> Term Contract -> Contract
    , mkCase :: Term Action -> Term Contract -> Case
    , mkBound :: BigInteger -> BigInteger -> Bound
    , mkDeposit :: AccountId -> Term Party -> Term Token -> Term Value -> Action
    , mkChoice :: ChoiceId -> Array (Term Bound) -> Action
    , mkNotify :: Term Observation -> Action
    , mkChoiceId :: String -> Term Party -> ChoiceId
    , mkValueId :: String -> ValueId
    , mkToken :: String -> String -> Token
    , mkPK :: String -> Party
    , mkRole :: String -> Party
    , mkAccount :: AccountId -> Payee
    , mkParty :: Term Party -> Payee
    , mkAndObs :: Term Observation -> Term Observation -> Observation
    , mkOrObs :: Term Observation -> Term Observation -> Observation
    , mkNotObs :: Term Observation -> Observation
    , mkChoseSomething :: ChoiceId -> Observation
    , mkValueGE :: Term Value -> Term Value -> Observation
    , mkValueGT :: Term Value -> Term Value -> Observation
    , mkValueLT :: Term Value -> Term Value -> Observation
    , mkValueLE :: Term Value -> Term Value -> Observation
    , mkValueEQ :: Term Value -> Term Value -> Observation
    , mkTrueObs :: Observation
    , mkFalseObs :: Observation
    , mkAvailableMoney :: AccountId -> Term Token -> Value
    , mkConstant :: BigInteger -> Value
    , mkNegValue :: Term Value -> Value
    , mkAddValue :: Term Value -> Term Value -> Value
    , mkSubValue :: Term Value -> Term Value -> Value
    , mkMulValue :: Term Value -> Term Value -> Value
    , mkRational :: BigInteger -> BigInteger -> Rational
    , mkScale :: TermWrapper Rational -> Term Value -> Value
    , mkChoiceValue :: ChoiceId -> Value
    , mkSlotIntervalStart :: Value
    , mkSlotIntervalEnd :: Value
    , mkUseValue :: TermWrapper ValueId -> Value
    , mkCond :: Term Observation -> Term Value -> Term Value -> Value
    }

helperFunctions :: forall a. HelperFunctions a
helperFunctions =
  { mkHole: mkHole
  , mkTerm: Term
  , mkTermWrapper: TermWrapper
  , getRange: getRange
  , mkBigInteger: BigInteger.fromInt
  , mkTimeout: \v pos -> TermWrapper (Slot (BigInteger.fromInt v)) pos
  , mkClose: Close
  , mkPay: Pay
  , mkWhen: When
  , mkIf: If
  , mkAssert: Assert
  , mkLet: Let
  , mkCase: Case
  , mkBound: Bound
  , mkDeposit: Deposit
  , mkChoice: Choice
  , mkNotify: Notify
  , mkChoiceId: ChoiceId
  , mkValueId: ValueId
  , mkToken: Token
  , mkPK: PK
  , mkRole: Role
  , mkAccount: Account
  , mkParty: Party
  , mkAndObs: AndObs
  , mkOrObs: OrObs
  , mkNotObs: NotObs
  , mkChoseSomething: ChoseSomething
  , mkValueGE: ValueGE
  , mkValueGT: ValueGT
  , mkValueLT: ValueLT
  , mkValueLE: ValueLE
  , mkValueEQ: ValueEQ
  , mkTrueObs: TrueObs
  , mkFalseObs: FalseObs
  , mkAvailableMoney: AvailableMoney
  , mkConstant: Constant
  , mkNegValue: NegValue
  , mkAddValue: AddValue
  , mkSubValue: SubValue
  , mkMulValue: MulValue
  , mkRational: Rational
  , mkScale: Scale
  , mkChoiceValue: ChoiceValue
  , mkSlotIntervalStart: SlotIntervalStart
  , mkSlotIntervalEnd: SlotIntervalEnd
  , mkUseValue: UseValue
  , mkCond: Cond
  }

data ContractParseError
  = EmptyInput
  | ContractParseError { message :: String, row :: Int, column :: Int, token :: String }

derive instance genericContractParseError :: Generic ContractParseError _

instance showContractParseError :: Show ContractParseError where
  show e = genericShow e

foreign import parse_ ::
  forall a.
  Fn5
    (Either ContractParseError (Term Contract))
    ({ message :: String, row :: Int, column :: Int, token :: String } -> Either ContractParseError (Term Contract))
    (Term Contract -> Either ContractParseError (Term Contract))
    (HelperFunctions a)
    String
    (Either ContractParseError (Term Contract))

parseContract :: String -> Either ContractParseError (Term Contract)
parseContract = runFn5 parse_ (Left EmptyInput) (Left <<< ContractParseError) Right helperFunctions

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
    -- this position info is incorrect however we don't use it anywhere at this time
    pure { result: Hole name Proxy zero, suffix }
  where
  nameChars = alphaNum <|> char '_'

term' :: forall a. Parser a -> Parser (Term a)
term' (Parser p) =
  Parser \{ pos, str } -> do
    { result, suffix } <- p { pos, str }
    let
      start = pos

      end = suffix.pos
    -- this position info is incorrect however we don't use it anywhere at this time
    pure { result: Term result zero, suffix }

termWrapper :: forall a. Parser a -> Parser (TermWrapper a)
termWrapper (Parser p) =
  Parser \{ pos, str } -> do
    { result, suffix } <- p { pos, str }
    let
      start = pos

      end = suffix.pos
    -- this position info is incorrect however we don't use it anywhere at this time
    pure { result: TermWrapper result zero, suffix }

parseTerm :: forall a. Parser a -> Parser (Term a)
parseTerm p = hole <|> (term' p)

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
    Nothing -> fail "not a valid BigInteger"

bigIntegerTerm :: Parser (Term BigInteger)
bigIntegerTerm = parseTerm bigInteger

valueId :: Parser ValueId
valueId = ValueId <$> text

slot :: Parser Slot
slot = Slot <$> maybeParens bigInteger

slotTerm :: Parser (Term Slot)
slotTerm = parseTerm slot

timeout :: Parser (TermWrapper Slot)
timeout = do
  result <- bigIntegerTerm
  case result of
    (Hole _ _ pos) -> fail ""
    (Term v pos) -> pure $ TermWrapper (Slot v) pos

accountId :: Parser AccountId
accountId = parseTerm $ parens party

choiceId :: Parser ChoiceId
choiceId = parens choiceId'

choiceId' :: Parser ChoiceId
choiceId' = do
  skipSpaces
  void $ string "ChoiceId"
  void someWhiteSpace
  first <- text
  void someWhiteSpace
  second <- parseTerm $ parens party
  skipSpaces
  pure $ ChoiceId first second

atomValue :: Parser Value
atomValue =
  (pure SlotIntervalStart <* string "SlotIntervalStart")
    <|> (pure SlotIntervalEnd <* string "SlotIntervalEnd")

rational :: Parser Rational
rational = do
  num <- bigInteger
  skipSpaces
  void $ string "%"
  skipSpaces
  denom <- bigInteger
  pure $ Rational num denom

-- `unit` is needed in order to enforce strict evaluation order
-- see https://stackoverflow.com/questions/36984245/undefined-value-reference-not-allowed-workaround/36991223#36991223
recValue :: Unit -> Parser Value
recValue _ =
  (AvailableMoney <$> (string "AvailableMoney" **> accountId) <**> parseTerm (parens token))
    <|> (Constant <$> (string "Constant" **> bigInteger))
    <|> (NegValue <$> (string "NegValue" **> value'))
    <|> (AddValue <$> (string "AddValue" **> value') <**> value')
    <|> (SubValue <$> (string "SubValue" **> value') <**> value')
    <|> (MulValue <$> (string "MulValue" **> value') <**> value')
    <|> do
        void $ string "Scale"
        skipSpaces
        s <- termWrapper (parens rational)
        skipSpaces
        v <- value'
        pure $ Scale s v
    <|> (ChoiceValue <$> (string "ChoiceValue" **> choiceId))
    <|> (UseValue <$> (string "UseValue" **> termWrapper valueId))
    <|> (Cond <$> (string "Cond" **> observation') <**> value' <**> value')
  where
  value' = parseTerm $ atomValue <|> fix (\p -> parens (recValue unit))

  observation' = parseTerm $ atomObservation <|> fix \p -> parens recObservation

value :: Unit -> Parser Value
value _ = atomValue <|> recValue unit

atomObservation :: Parser Observation
atomObservation =
  (pure TrueObs <* string "TrueObs")
    <|> (pure FalseObs <* string "FalseObs")

recObservation :: Parser Observation
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
  observation' = parseTerm $ atomObservation <|> fix \p -> parens recObservation

  value' = parseTerm $ atomValue <|> fix (\p -> parens (value unit))

observation :: Parser Observation
observation = atomObservation <|> recObservation

payee :: Parser Payee
payee =
  (Account <$> (string "Account" **> accountId))
    <|> (Party <$> (string "Party" **> parseTerm (parens party)))

pubkey :: Parser PubKey
pubkey = text

party :: Parser Party
party =
  (PK <$> (string "PK" **> pubkey))
    <|> (Role <$> (string "Role" **> tokenName))

currencySymbol :: Parser CurrencySymbol
currencySymbol = text

tokenName :: Parser TokenName
tokenName = text

token :: Parser Token
token = do
  skipSpaces
  void $ string "Token"
  void someWhiteSpace
  first <- text
  void someWhiteSpace
  second <- text
  skipSpaces
  pure $ Token first second

bound :: Parser Bound
bound = do
  skipSpaces
  void $ string "Bound"
  void someWhiteSpace
  first <- bigInteger
  void someWhiteSpace
  second <- bigInteger
  skipSpaces
  pure (Bound first second)

action :: Parser Action
action =
  (Deposit <$> (string "Deposit" **> accountId) <**> parseTerm (parens party) <**> parseTerm (parens token) <**> value')
    <|> (Choice <$> (string "Choice" **> choiceId) <**> array (maybeParens (parseTerm bound)))
    <|> (Notify <$> (string "Notify" **> observation'))
  where
  observation' = parseTerm $ atomObservation <|> fix \p -> parens recObservation

  value' = parseTerm $ atomValue <|> fix (\p -> parens (recValue unit))

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
  ( Pay <$> (string "Pay" **> accountId)
      <**> parseTerm (parens payee)
      <**> parseTerm (parens token)
      <**> value'
      <**> contract'
  )
    <|> (If <$> (string "If" **> observation') <**> contract' <**> contract')
    <|> (When <$> (string "When" **> (array (maybeParens (parseTerm case')))) <**> timeout <**> contract')
    <|> (Let <$> (string "Let" **> termWrapper valueId) <**> value' <**> contract')
    <|> (Assert <$> (string "Assert" **> observation') <**> contract')
    <|> (fail "not a valid Contract")
  where
  contract' = parseTerm $ atomContract <|> fix \p -> parens recContract

  observation' = parseTerm $ atomObservation <|> fix \p -> parens observation

  value' = parseTerm $ atomValue <|> fix (\p -> parens (value unit))

contract :: Parser Contract
contract = do
  skipSpaces
  c <- (atomContract <|> recContract)
  skipSpaces
  pure c

testString :: String
testString =
  """When [
  (Case
     (Deposit
        "alice" "alice"
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
                             (ChoiceId "1" "alice"))
                          (ChoiceValue
                             (ChoiceId "1" "bob")))
                       (If
                          (ValueEQ
                             (ChoiceValue
                                (ChoiceId "1" "alice"))
                             (Constant 0))
                          (Pay
                             "alice"
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
                                   "alice"
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
                             "alice"
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
                             (ChoiceId "1" "alice"))
                          (ChoiceValue
                             (ChoiceId "1" "bob")))
                       (If
                          (ValueEQ
                             (ChoiceValue
                                (ChoiceId "1" "alice"))
                             (Constant 0))
                          (Pay
                             "alice"
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
                                   "alice"
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
                             "alice"
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
accountIdValue = parseToValue (parens party)

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
testTransactionInputParsing = "[TransactionInput { txInterval = (2 , 8), txInputs = [ (IDeposit (Role \"investor\") (Role \"investor\") (Token \"\" \"\") 850)]}]"

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
              <|> (TransactionAssertionFailed <$ (string "TransactionAssertionFailed"))
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
    (Role "investor")
    (Party
      (Role "investor"))
    (Token "" "") 1000 1300)]"""
