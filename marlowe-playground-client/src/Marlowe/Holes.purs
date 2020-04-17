module Marlowe.Holes where

import Prelude
import Data.Array (foldMap, foldl, mapWithIndex)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.Enum (class BoundedEnum, class Enum, upFromIncluding)
import Data.Foldable (intercalate)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Bounded (genericBottom, genericTop)
import Data.Generic.Rep.Enum (genericCardinality, genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Generic.Rep.Show (genericShow)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..), length, stripPrefix, stripSuffix, trim)
import Data.String.Extra (unlines)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Marlowe.Semantics (ChosenNum, Money, Rational, PubKey, Slot(..), TokenName)
import Marlowe.Semantics as S
import Monaco (CompletionItem, IRange, completionItemKind)
import Text.Parsing.StringParser (Pos)
import Text.Parsing.StringParser.Basic (lines, replaceInPosition)
import Text.Pretty (class Args, class Pretty, genericHasArgs, genericHasNestedArgs, genericPretty, hasArgs, hasNestedArgs, pretty)
import Text.Pretty as P
import Type.Proxy (Proxy(..))

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
  | ObservationType
  | ContractType
  | BoundType
  | TokenType
  | PartyType

derive instance eqMarloweType :: Eq MarloweType

derive instance genericMarloweType :: Generic MarloweType _

instance showMarloweType :: Show MarloweType where
  show = genericShow

derive instance ordMarloweType :: Ord MarloweType

instance enumMarloweType :: Enum MarloweType where
  succ = genericSucc
  pred = genericPred

instance boundedMarloweType :: Bounded MarloweType where
  bottom = genericBottom
  top = genericTop

instance boundedEnumMarloweType :: BoundedEnum MarloweType where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum

allMarloweTypes :: Array MarloweType
allMarloweTypes = upFromIncluding bottom

readMarloweType :: String -> Maybe MarloweType
readMarloweType "StringType" = Just StringType

readMarloweType "BigIntegerType" = Just BigIntegerType

readMarloweType "SlotType" = Just SlotType

readMarloweType "AccountIdType" = Just AccountIdType

readMarloweType "ChoiceIdType" = Just ChoiceIdType

readMarloweType "ValueIdType" = Just ValueIdType

readMarloweType "ActionType" = Just ActionType

readMarloweType "PayeeType" = Just PayeeType

readMarloweType "CaseType" = Just CaseType

readMarloweType "ValueType" = Just ValueType

readMarloweType "ObservationType" = Just ObservationType

readMarloweType "ContractType" = Just ContractType

readMarloweType "BoundType" = Just BoundType

readMarloweType "TokenType" = Just TokenType

readMarloweType "PartyType" = Just PartyType

readMarloweType _ = Nothing

data Argument
  = ArrayArg String
  | DataArg String
  | DefaultString String
  | DefaultNumber BigInteger
  | NewtypeArg

getMarloweConstructors :: MarloweType -> Map String (Array Argument)
getMarloweConstructors StringType = Map.singleton "String" [ NewtypeArg ]

getMarloweConstructors BigIntegerType = Map.singleton "Integer" [ NewtypeArg ]

getMarloweConstructors SlotType = Map.singleton "Integer" [ NewtypeArg ]

getMarloweConstructors AccountIdType = Map.singleton "AccountId" [ DefaultNumber zero, DataArg "accHolder" ]

getMarloweConstructors ChoiceIdType = Map.singleton "ChoiceId" [ DefaultString "choiceNumber", DataArg "choiceOwner" ]

getMarloweConstructors ValueIdType = mempty

getMarloweConstructors ActionType =
  Map.fromFoldable
    [ (Tuple "Deposit" [ DataArg "accountId", DataArg "party", DataArg "token", DataArg "value" ])
    , (Tuple "Choice" [ DataArg "choiceId", ArrayArg "bounds" ])
    , (Tuple "Notify" [ DataArg "observation" ])
    ]

getMarloweConstructors PayeeType =
  Map.fromFoldable
    [ (Tuple "Account" [ DataArg "accountId" ])
    , (Tuple "Party" [ DataArg "party" ])
    ]

getMarloweConstructors CaseType = Map.singleton "Case" [ DataArg "action", DataArg "contract" ]

getMarloweConstructors ValueType =
  Map.fromFoldable
    [ (Tuple "AvailableMoney" [ DataArg "accountId", DataArg "token" ])
    , (Tuple "Constant" [ DefaultNumber zero ])
    , (Tuple "NegValue" [ DataArg "value" ])
    , (Tuple "AddValue" [ DataArg "value", DataArg "value" ])
    , (Tuple "SubValue" [ DataArg "value", DataArg "value" ])
    , (Tuple "Scale" [ DataArg "rational", DataArg "value" ])
    , (Tuple "ChoiceValue" [ DataArg "choiceId", DataArg "value" ])
    , (Tuple "SlotIntervalStart" [])
    , (Tuple "SlotIntervalEnd" [])
    , (Tuple "UseValue" [ DefaultString "valueId" ])
    ]

getMarloweConstructors ObservationType =
  Map.fromFoldable
    [ (Tuple "AndObs" [ DataArg "observation", DataArg "observation" ])
    , (Tuple "OrObs" [ DataArg "observation", DataArg "observation" ])
    , (Tuple "NotObs" [ DataArg "observation" ])
    , (Tuple "ChoseSomething" [ DataArg "choiceId" ])
    , (Tuple "ValueGE" [ DataArg "value", DataArg "value" ])
    , (Tuple "ValueGT" [ DataArg "value", DataArg "value" ])
    , (Tuple "ValueLE" [ DataArg "value", DataArg "value" ])
    , (Tuple "ValueLT" [ DataArg "value", DataArg "value" ])
    , (Tuple "ValueEQ" [ DataArg "value", DataArg "value" ])
    , (Tuple "TrueObs" [])
    , (Tuple "FalseObs" [])
    ]

getMarloweConstructors ContractType =
  Map.fromFoldable
    [ (Tuple "Close" [])
    , (Tuple "Pay" [ DataArg "accountId", DataArg "payee", DataArg "token", DataArg "value", DataArg "contract" ])
    , (Tuple "If" [ DataArg "observation", DataArg "contract", DataArg "contract" ])
    , (Tuple "When" [ ArrayArg "case", DefaultNumber zero, DataArg "contract" ])
    , (Tuple "Let" [ DefaultString "valueId", DataArg "value", DataArg "contract" ])
    ]

getMarloweConstructors BoundType = Map.singleton "Bound" [ DefaultNumber zero, DefaultNumber zero ]

getMarloweConstructors TokenType = Map.singleton "Token" [ DefaultString "", DefaultString "" ]

getMarloweConstructors PartyType =
  Map.fromFoldable
    [ (Tuple "PK" [ DefaultString "pubKey" ])
    , (Tuple "Role" [ DefaultString "token" ])
    ]

allMarloweConstructors :: Map String (Array Argument)
allMarloweConstructors = foldl (\acc mt -> getMarloweConstructors mt <> acc) mempty allMarloweTypes

-- Based on a String representation of a constructor get the MarloweType
-- "Close" -> ContractType
-- "PK" -> PartyType
getMarloweTypeFromConstructor :: String -> Maybe MarloweType
getMarloweTypeFromConstructor constructor =
  let
    f t = Set.member constructor (Map.keys (getMarloweConstructors t))
  in
    Array.find f allMarloweTypes

-- | Creates a String consisting of the data constructor name followed by argument holes
--   e.g. "When [ ?case_10 ] ?timeout_11 ?contract_12"
constructMarloweType :: String -> MarloweHole -> Map String (Array Argument) -> String
constructMarloweType constructorName (MarloweHole { row, column }) m = case Map.lookup constructorName m of
  Nothing -> ""
  Just [] -> constructorName
  Just vs -> parens row column $ constructorName <> " " <> intercalate " " (mapWithIndex showArgument vs)
  where
  showArgument i (ArrayArg arg) = "[ ?" <> arg <> "_" <> show row <> "_" <> show column <> "_" <> show i <> " ]"

  showArgument i (DataArg arg) = "?" <> arg <> "_" <> show row <> "_" <> show column <> "_" <> show i

  showArgument _ (DefaultString arg) = "\"" <> arg <> "\""

  showArgument _ (DefaultNumber arg) = show arg

  showArgument _ NewtypeArg = ""

  parens 1 1 text = text

  parens _ _ text = "(" <> text <> ")"

mkHole :: forall a. String -> { row :: Pos, column :: Pos } -> Term a
mkHole name position = Hole name Proxy position

data Term a
  = Term a { row :: Pos, column :: Pos }
  | Hole String (Proxy a) { row :: Pos, column :: Pos }

derive instance genericTerm :: Generic (Term a) _

derive instance eqTerm :: Eq a => Eq (Term a)

derive instance ordTerm :: Ord a => Ord (Term a)

instance showTerm :: Show a => Show (Term a) where
  show (Term a _) = show a
  show (Hole name _ _) = "?" <> name

instance prettyTerm :: Pretty a => Pretty (Term a) where
  pretty (Term a _) = P.pretty a
  pretty (Hole name _ _) = P.text $ "?" <> name

instance hasArgsTerm :: Args a => Args (Term a) where
  hasArgs (Term a _) = hasArgs a
  hasArgs _ = false
  hasNestedArgs (Term a _) = hasNestedArgs a
  hasNestedArgs _ = false

getPosition :: forall a. Term a -> { row :: Pos, column :: Pos }
getPosition (Term _ pos) = pos

getPosition (Hole _ _ pos) = pos

data TermWrapper a
  = TermWrapper a { row :: Pos, column :: Pos }

derive instance genericTermWrapper :: Generic a r => Generic (TermWrapper a) _

instance eqTermWrapper :: Eq a => Eq (TermWrapper a) where
  eq (TermWrapper a _) (TermWrapper b _) = eq a b

instance ordTermWrapper :: Ord a => Ord (TermWrapper a) where
  compare (TermWrapper a _) (TermWrapper b _) = compare a b

instance showTermWrapper :: Show a => Show (TermWrapper a) where
  show (TermWrapper a _) = show a

instance prettyTermWrapper :: Pretty a => Pretty (TermWrapper a) where
  pretty (TermWrapper a _) = pretty a

instance hasArgsTermWrapper :: Args a => Args (TermWrapper a) where
  hasArgs (TermWrapper _ _) = false
  hasNestedArgs (TermWrapper _ _) = false

instance fromTermTermWrapper :: FromTerm a b => FromTerm (TermWrapper a) b where
  fromTerm (TermWrapper a _) = fromTerm a

-- a concrete type for holes only
data MarloweHole
  = MarloweHole
    { name :: String
    , marloweType :: MarloweType
    , row :: Pos
    , column :: Pos
    }

derive instance genericMarloweHole :: Generic MarloweHole _

derive instance eqMarloweHole :: Eq MarloweHole

instance ordMarloweHole :: Ord MarloweHole where
  compare (MarloweHole { row: la, column: ca }) (MarloweHole { row: lb, column: cb }) = if la == lb then compare ca cb else compare la lb

instance showMarloweHole :: Show MarloweHole where
  show = genericShow

class IsMarloweType a where
  marloweType :: Proxy a -> MarloweType

instance stringIsMarloweType :: IsMarloweType String where
  marloweType _ = StringType

instance bigIntegerIsMarloweType :: IsMarloweType BigInteger where
  marloweType _ = BigIntegerType

marloweHoleToSuggestion :: Boolean -> IRange -> MarloweHole -> String -> CompletionItem
marloweHoleToSuggestion stripParens range firstHole@(MarloweHole { marloweType }) constructorName =
  let
    kind = completionItemKind "Constructor"

    m = getMarloweConstructors marloweType

    fullInsertText = constructMarloweType constructorName firstHole m

    insertText =
      if stripParens then
        fromMaybe fullInsertText
          $ do
              withoutPrefix <- stripPrefix (Pattern "(") $ trim fullInsertText
              withoutSuffix <- stripSuffix (Pattern ")") withoutPrefix
              pure withoutSuffix
      else
        fullInsertText
  in
    { label: constructorName, kind, range, insertText }

holeSuggestions :: Boolean -> IRange -> MarloweHole -> Array CompletionItem
holeSuggestions stripParens range marloweHole@(MarloweHole { name, marloweType }) =
  let
    marloweHoles = getMarloweConstructors marloweType
  in
    map (marloweHoleToSuggestion stripParens range marloweHole) $ Set.toUnfoldable $ Map.keys marloweHoles

-- a Monoid for collecting Holes
newtype Holes
  = Holes (Map String (Set MarloweHole))

derive instance genericHoles :: Generic Holes _

derive instance newtypeHoles :: Newtype Holes _

derive newtype instance showHoles :: Show Holes

instance semigroupHoles :: Semigroup Holes where
  append (Holes a) (Holes b) = Holes (Map.unionWith append a b)

derive newtype instance monoidHoles :: Monoid Holes

insertHole :: forall a. IsMarloweType a => Term a -> Holes -> Holes
insertHole (Term _ _) m = m

insertHole (Hole name proxy { row, column }) (Holes m) = Holes $ Map.alter f name m
  where
  marloweHole = MarloweHole { name, marloweType: (marloweType proxy), row, column }

  f v = Just (Set.insert marloweHole $ fromMaybe mempty v)

class HasMarloweHoles a where
  getHoles :: a -> Holes -> Holes

instance termHasMarloweHoles :: (IsMarloweType a, HasMarloweHoles a) => HasMarloweHoles (Term a) where
  getHoles (Term a _) m = getHoles a m
  getHoles h m = insertHole h m

instance arrayHasMarloweHoles :: HasMarloweHoles a => HasMarloweHoles (Array a) where
  getHoles as m = foldMap (\a -> getHoles a m) as

-- Parsable versions of the Marlowe types
-- Timeout is special, we want to be able to show warnings from the linter in the position
-- however as it is just a number we don't want to be able to have holes since that makes
-- working with blockly more difficult (since number values can't be null)
data Timeout
  = Timeout Slot { row :: Pos, column :: Pos }

derive instance genericTimeout :: Generic Timeout _

instance eqTimeout :: Eq Timeout where
  eq (Timeout a _) (Timeout b _) = eq a b

instance ordTimeout :: Ord Timeout where
  compare (Timeout a _) (Timeout b _) = compare a b

instance showTimeout :: Show Timeout where
  show (Timeout (Slot v) _) = show v

instance prettyTimeout :: Pretty Timeout where
  pretty (Timeout (Slot slot) _) = pretty slot

instance hasArgsTimeout :: Args Timeout where
  hasArgs (Timeout slot _) = false
  hasNestedArgs (Timeout slot _) = false

data Bound
  = Bound BigInteger BigInteger

derive instance genericBound :: Generic Bound _

instance showBound :: Show Bound where
  show v = genericShow v

instance prettyBound :: Pretty Bound where
  pretty v = genericPretty v

instance hasArgsBound :: Args Bound where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

instance boundFromTerm :: FromTerm Bound S.Bound where
  fromTerm (Bound a b) = S.Bound <$> pure a <*> pure b

instance boundIsMarloweType :: IsMarloweType Bound where
  marloweType _ = BoundType

instance boundHasMarloweHoles :: HasMarloweHoles Bound where
  getHoles (Bound a b) m = m

data Party
  = PK PubKey
  | Role TokenName

derive instance genericParty :: Generic Party _

instance showParty :: Show Party where
  show v = genericShow v

instance prettyParty :: Pretty Party where
  pretty = genericPretty

instance hasArgsParty :: Args Party where
  hasArgs = genericHasArgs
  hasNestedArgs = genericHasNestedArgs

instance partyFromTerm :: FromTerm Party S.Party where
  fromTerm (PK b) = pure $ S.PK b
  fromTerm (Role b) = pure $ S.Role b

instance partyIsMarloweType :: IsMarloweType Party where
  marloweType _ = PartyType

instance partyHasMarloweHoles :: HasMarloweHoles Party where
  getHoles (PK a) m = m
  getHoles (Role a) m = m

data AccountId
  = AccountId BigInteger (Term Party)

derive instance genericAccountId :: Generic AccountId _

derive instance eqAccountId :: Eq AccountId

derive instance ordAccountId :: Ord AccountId

instance showAccountId :: Show AccountId where
  show v = genericShow v

instance prettyAccountId :: Pretty AccountId where
  pretty = genericPretty

instance hasArgsAccountId :: Args AccountId where
  hasArgs = genericHasArgs
  hasNestedArgs = genericHasNestedArgs

instance accountIdFromTerm :: FromTerm AccountId S.AccountId where
  fromTerm (AccountId b (Term c _)) = S.AccountId <$> pure b <*> fromTerm c
  fromTerm _ = Nothing

instance accountIdIsMarloweType :: IsMarloweType AccountId where
  marloweType _ = AccountIdType

instance accountIdHasMarloweHoles :: HasMarloweHoles AccountId where
  getHoles (AccountId a b) m = m <> getHoles b m

data Token
  = Token String String

derive instance genericToken :: Generic Token _

derive instance eqToken :: Eq Token

derive instance ordToken :: Ord Token

instance showToken :: Show Token where
  show tok = genericShow tok

instance prettyToken :: Pretty Token where
  pretty = genericPretty

instance hasArgsToken :: Args Token where
  hasArgs = genericHasArgs
  hasNestedArgs = genericHasNestedArgs

instance tokenFromTerm :: FromTerm Token S.Token where
  fromTerm (Token b c) = pure $ S.Token b c

instance tokenIsMarloweType :: IsMarloweType Token where
  marloweType _ = TokenType

instance tokenHasMarloweHoles :: HasMarloweHoles Token where
  getHoles (Token a b) m = m

data ChoiceId
  = ChoiceId String (Term Party)

derive instance genericChoiceId :: Generic ChoiceId _

derive instance eqChoiceId :: Eq ChoiceId

derive instance ordChoiceId :: Ord ChoiceId

instance showChoiceId :: Show ChoiceId where
  show v = genericShow v

instance prettyChoiceId :: Pretty ChoiceId where
  pretty = genericPretty

instance hasArgsChoiceId :: Args ChoiceId where
  hasArgs = genericHasArgs
  hasNestedArgs = genericHasNestedArgs

instance choiceIdFromTerm :: FromTerm ChoiceId S.ChoiceId where
  fromTerm (ChoiceId a (Term b _)) = S.ChoiceId <$> pure a <*> fromTerm b
  fromTerm _ = Nothing

instance choiceIdIsMarloweType :: IsMarloweType ChoiceId where
  marloweType _ = ChoiceIdType

instance choiceIdHasMarloweHoles :: HasMarloweHoles ChoiceId where
  getHoles (ChoiceId a b) m = m <> insertHole b m

data Action
  = Deposit (Term AccountId) (Term Party) (Term Token) (Term Value)
  | Choice (Term ChoiceId) (Array (Term Bound))
  | Notify (Term Observation)

derive instance genericAction :: Generic Action _

instance showAction :: Show Action where
  show v = genericShow v

instance prettyAction :: Pretty Action where
  pretty v = genericPretty v

instance hasArgsAction :: Args Action where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

instance actionFromTerm :: FromTerm Action S.Action where
  fromTerm (Deposit a b c d) = S.Deposit <$> fromTerm a <*> fromTerm b <*> fromTerm c <*> fromTerm d
  fromTerm (Choice a b) = S.Choice <$> fromTerm a <*> (traverse fromTerm b)
  fromTerm (Notify a) = S.Notify <$> fromTerm a

instance actionMarloweType :: IsMarloweType Action where
  marloweType _ = ActionType

data Payee
  = Account (Term AccountId)
  | Party (Term Party)

derive instance genericPayee :: Generic Payee _

derive instance eqParty :: Eq Party

derive instance ordParty :: Ord Party

instance showPayee :: Show Payee where
  show v = genericShow v

instance prettyPayee :: Pretty Payee where
  pretty v = genericPretty v

instance hasArgsPayee :: Args Payee where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

instance payeeFromTerm :: FromTerm Payee S.Payee where
  fromTerm (Account a) = S.Account <$> fromTerm a
  fromTerm (Party (Term a _)) = S.Party <$> fromTerm a
  fromTerm _ = Nothing

instance payeeMarloweType :: IsMarloweType Payee where
  marloweType _ = PayeeType

instance payeeHasMarloweHoles :: HasMarloweHoles Payee where
  getHoles (Account a) m = getHoles a m
  getHoles (Party a) m = insertHole a m

data Case
  = Case (Term Action) (Term Contract)

derive instance genericCase :: Generic Case _

instance showCase :: Show Case where
  show v = genericShow v

instance prettyCase :: Pretty Case where
  pretty v = genericPretty v

instance hasArgsCase :: Args Case where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

instance caseFromTerm :: FromTerm Case S.Case where
  fromTerm (Case a b) = S.Case <$> fromTerm a <*> fromTerm b

instance caseMarloweType :: IsMarloweType Case where
  marloweType _ = CaseType

data Value
  = AvailableMoney (Term AccountId) (Term Token)
  | Constant BigInteger
  | NegValue (Term Value)
  | AddValue (Term Value) (Term Value)
  | SubValue (Term Value) (Term Value)
  | Scale (Term Rational) (Term Value)
  | ChoiceValue (Term ChoiceId) (Term Value)
  | SlotIntervalStart
  | SlotIntervalEnd
  | UseValue (TermWrapper ValueId)

derive instance genericValue :: Generic Value _

derive instance eqValue :: Eq Value

derive instance ordValue :: Ord Value

instance showValue :: Show Value where
  show v = genericShow v

instance prettyValue :: Pretty Value where
  pretty v = genericPretty v

instance hasArgsValue :: Args Value where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

instance valueFromTerm :: FromTerm Value S.Value where
  fromTerm (AvailableMoney a b) = S.AvailableMoney <$> fromTerm a <*> fromTerm b
  fromTerm (Constant a) = pure $ S.Constant a
  fromTerm (NegValue a) = S.NegValue <$> fromTerm a
  fromTerm (AddValue a b) = S.AddValue <$> fromTerm a <*> fromTerm b
  fromTerm (SubValue a b) = S.SubValue <$> fromTerm a <*> fromTerm b
  fromTerm (Scale a b) = S.Scale <$> termToValue a <*> fromTerm b
  fromTerm (ChoiceValue a b) = S.ChoiceValue <$> fromTerm a <*> fromTerm b
  fromTerm SlotIntervalStart = pure S.SlotIntervalStart
  fromTerm SlotIntervalEnd = pure S.SlotIntervalEnd
  fromTerm (UseValue a) = S.UseValue <$> fromTerm a

instance valueIsMarloweType :: IsMarloweType Value where
  marloweType _ = ValueType

data Input
  = IDeposit (Term AccountId) (Term Party) (Term Money)
  | IChoice (Term ChoiceId) (Term ChosenNum)
  | INotify

data Observation
  = AndObs (Term Observation) (Term Observation)
  | OrObs (Term Observation) (Term Observation)
  | NotObs (Term Observation)
  | ChoseSomething (Term ChoiceId)
  | ValueGE (Term Value) (Term Value)
  | ValueGT (Term Value) (Term Value)
  | ValueLT (Term Value) (Term Value)
  | ValueLE (Term Value) (Term Value)
  | ValueEQ (Term Value) (Term Value)
  | TrueObs
  | FalseObs

derive instance genericObservation :: Generic Observation _

derive instance eqObservation :: Eq Observation

derive instance ordObservation :: Ord Observation

instance showObservation :: Show Observation where
  show v = genericShow v

instance prettyObservation :: Pretty Observation where
  pretty v = genericPretty v

instance hasArgsObservation :: Args Observation where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

instance fromTermTerm :: FromTerm a b => FromTerm (Term a) b where
  fromTerm (Term a _) = fromTerm a
  fromTerm _ = Nothing

instance observationFromTerm :: FromTerm Observation S.Observation where
  fromTerm (AndObs a b) = S.AndObs <$> fromTerm a <*> fromTerm b
  fromTerm (OrObs a b) = S.OrObs <$> fromTerm a <*> fromTerm b
  fromTerm (NotObs a) = S.NotObs <$> fromTerm a
  fromTerm (ChoseSomething a) = S.ChoseSomething <$> fromTerm a
  fromTerm (ValueGE a b) = S.ValueGE <$> fromTerm a <*> fromTerm b
  fromTerm (ValueGT a b) = S.ValueGT <$> fromTerm a <*> fromTerm b
  fromTerm (ValueLT a b) = S.ValueLT <$> fromTerm a <*> fromTerm b
  fromTerm (ValueLE a b) = S.ValueLE <$> fromTerm a <*> fromTerm b
  fromTerm (ValueEQ a b) = S.ValueEQ <$> fromTerm a <*> fromTerm b
  fromTerm TrueObs = pure S.TrueObs
  fromTerm FalseObs = pure S.FalseObs

instance observationIsMarloweType :: IsMarloweType Observation where
  marloweType _ = ObservationType

data Contract
  = Close
  | Pay (Term AccountId) (Term Payee) (Term Token) (Term Value) (Term Contract)
  | If (Term Observation) (Term Contract) (Term Contract)
  | When (Array (Term Case)) Timeout (Term Contract)
  | Let (TermWrapper ValueId) (Term Value) (Term Contract)

derive instance genericContract :: Generic Contract _

instance showContract :: Show Contract where
  show v = genericShow v

instance prettyContract :: Pretty Contract where
  pretty v = genericPretty v

instance hasArgsContract :: Args Contract where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

instance contractFromTerm :: FromTerm Contract S.Contract where
  fromTerm Close = pure S.Close
  fromTerm (Pay a b c d e) = S.Pay <$> fromTerm a <*> fromTerm b <*> fromTerm c <*> fromTerm d <*> fromTerm e
  fromTerm (If a b c) = S.If <$> fromTerm a <*> fromTerm b <*> fromTerm c
  fromTerm (When as (Timeout b _) c) = S.When <$> (traverse fromTerm as) <*> pure b <*> fromTerm c
  fromTerm (Let a b c) = S.Let <$> fromTerm a <*> fromTerm b <*> fromTerm c

instance contractIsMarloweType :: IsMarloweType Contract where
  marloweType _ = ContractType

newtype ValueId
  = ValueId String

derive instance genericValueId :: Generic ValueId _

derive instance newtypeValueId :: Newtype ValueId _

derive newtype instance eqValueId :: Eq ValueId

derive newtype instance ordValueId :: Ord ValueId

instance showValueId :: Show ValueId where
  show (ValueId valueId') = show valueId'

instance prettyValueId :: Pretty ValueId where
  pretty (ValueId valueId) = P.text $ show valueId

instance hasArgsValueId :: Args ValueId where
  hasArgs _ = false
  hasNestedArgs _ = false

instance valueIdFromTerm :: FromTerm ValueId S.ValueId where
  fromTerm (ValueId a) = pure $ S.ValueId a

instance valueIdIsMarloweType :: IsMarloweType ValueId where
  marloweType _ = ValueIdType

instance valueIdHasMarloweHoles :: HasMarloweHoles ValueId where
  getHoles _ m = m

termToValue :: forall a. Term a -> Maybe a
termToValue (Term a _) = Just a

termToValue _ = Nothing

class FromTerm a b where
  fromTerm :: a -> Maybe b

instance slotMarloweType :: IsMarloweType Slot where
  marloweType _ = SlotType

-- Replace all holes of a certain name with the value
replaceInPositions :: String -> MarloweHole -> Array MarloweHole -> String -> String
replaceInPositions constructor firstHole@(MarloweHole { marloweType, name }) holes currentContract = unlines $ mapWithIndex go (lines currentContract)
  where
  go :: Int -> String -> String
  go idx currentLine =
    let
      m = getMarloweConstructors marloweType

      holeString = constructMarloweType constructor firstHole m

      stringLengthDifference = (length holeString) - (length name)

      (final /\ _) =
        foldl
          ( \(currString /\ currLength) hole@(MarloweHole { name, row, column }) ->
              if row == (idx + 1) then
                let
                  newString = replaceInPosition { start: column - 1 + currLength, end: column + currLength + (length name), string: currString, replacement: holeString }

                  newLength = currLength + stringLengthDifference
                in
                  (newString /\ newLength)
              else
                (currString /\ currLength)
          )
          (currentLine /\ 0)
          holes
    in
      final
