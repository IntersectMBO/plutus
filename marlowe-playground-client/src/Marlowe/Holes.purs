module Marlowe.Holes where

import Prelude
import Control.Monad.Except.Extra (noteT)
import Data.Array (foldMap)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.Enum (class BoundedEnum, class Enum, upFromIncluding)
import Data.Foldable (intercalate)
import Data.Function (on)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Bounded (genericBottom, genericTop)
import Data.Generic.Rep.Enum (genericCardinality, genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Lens', over)
import Data.Lens.Record (prop)
import Data.List.NonEmpty as NEL
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, unwrap)
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..), contains, splitAt, toLower)
import Data.String.CodeUnits (dropRight)
import Data.Symbol (SProxy(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Foreign (readString)
import Foreign.Generic (class Decode, class Encode, ForeignError(..), decode, encode)
import Marlowe.Semantics (PubKey, Rational(..), Slot, TokenName)
import Marlowe.Semantics as S
import Monaco (CompletionItem, IRange, completionItemKind)
import Text.Extra as Text
import Text.Pretty (class Args, class Pretty, genericHasArgs, genericHasNestedArgs, genericPretty, hasArgs, hasNestedArgs, pretty)
import Text.Pretty as P
import Type.Proxy (Proxy(..))

-- | These are Marlowe types that can be represented as holes
data MarloweType
  = ChoiceIdType
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

instance encodeMarloweType :: Encode MarloweType where
  encode = encode <<< show

instance decodeMarloweType :: Decode MarloweType where
  decode t = do
    s <- readString t
    noteT (NEL.singleton (ForeignError (s <> " is not a valid MarloweType"))) $ readMarloweType s

allMarloweTypes :: Array MarloweType
allMarloweTypes = upFromIncluding bottom

readMarloweType :: String -> Maybe MarloweType
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

-- | To make a name for a hole we show the type, make the first letter lower case and then drop the "Type" at the end
mkArgName :: MarloweType -> String
mkArgName t = case splitAt 1 (show t) of
  { before, after } -> toLower before <> dropRight 4 after

data Argument
  = ArrayArg String
  | EmptyArrayArg
  | DataArg MarloweType
  | NamedDataArg String
  | DataArgIndexed Int MarloweType
  | DefaultString String
  | DefaultNumber BigInteger
  | DefaultRational Rational
  | NewtypeArg
  | GenArg MarloweType

getMarloweConstructors :: MarloweType -> Map String (Array Argument)
getMarloweConstructors ChoiceIdType = Map.singleton "ChoiceId" [ DefaultString "choiceNumber", DataArg PartyType ]

getMarloweConstructors ValueIdType = mempty

getMarloweConstructors ActionType =
  Map.fromFoldable
    [ (Tuple "Deposit" [ DataArg PartyType, NamedDataArg "from_party", DataArg TokenType, DataArg ValueType ])
    , (Tuple "Choice" [ GenArg ChoiceIdType, ArrayArg "bounds" ])
    , (Tuple "Notify" [ DataArg ObservationType ])
    ]

getMarloweConstructors PayeeType =
  Map.fromFoldable
    [ (Tuple "Account" [ DataArg PartyType ])
    , (Tuple "Party" [ DataArg PartyType ])
    ]

getMarloweConstructors CaseType = Map.singleton "Case" [ DataArg ActionType, DataArg ContractType ]

getMarloweConstructors ValueType =
  Map.fromFoldable
    [ (Tuple "AvailableMoney" [ DataArg PartyType, DataArg TokenType ])
    , (Tuple "Constant" [ DefaultNumber zero ])
    , (Tuple "NegValue" [ DataArg ValueType ])
    , (Tuple "AddValue" [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "SubValue" [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "MulValue" [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "Scale" [ DefaultRational (Rational one one), DataArg ValueType ])
    , (Tuple "ChoiceValue" [ GenArg ChoiceIdType ])
    , (Tuple "SlotIntervalStart" [])
    , (Tuple "SlotIntervalEnd" [])
    , (Tuple "UseValue" [ DefaultString "valueId" ])
    , (Tuple "Cond" [ DataArg ObservationType, DataArg ValueType, DataArg ValueType ])
    ]

getMarloweConstructors ObservationType =
  Map.fromFoldable
    [ (Tuple "AndObs" [ DataArgIndexed 1 ObservationType, DataArgIndexed 2 ObservationType ])
    , (Tuple "OrObs" [ DataArgIndexed 1 ObservationType, DataArgIndexed 2 ObservationType ])
    , (Tuple "NotObs" [ DataArg ObservationType ])
    , (Tuple "ChoseSomething" [ GenArg ChoiceIdType ])
    , (Tuple "ValueGE" [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "ValueGT" [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "ValueLE" [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "ValueLT" [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "ValueEQ" [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "TrueObs" [])
    , (Tuple "FalseObs" [])
    ]

getMarloweConstructors ContractType =
  Map.fromFoldable
    [ (Tuple "Close" [])
    , (Tuple "Pay" [ DataArg PartyType, DataArg PayeeType, DataArg TokenType, DataArg ValueType, DataArg ContractType ])
    , (Tuple "If" [ DataArg ObservationType, DataArgIndexed 1 ContractType, DataArgIndexed 2 ContractType ])
    , (Tuple "When" [ EmptyArrayArg, DefaultNumber zero, DataArg ContractType ])
    , (Tuple "Let" [ DefaultString "valueId", DataArg ValueType, DataArg ContractType ])
    , (Tuple "Assert" [ DataArg ObservationType, DataArg ContractType ])
    ]

getMarloweConstructors BoundType = Map.singleton "Bound" [ DefaultNumber zero, DefaultNumber zero ]

getMarloweConstructors TokenType = Map.singleton "Token" [ DefaultString "", DefaultString "" ]

getMarloweConstructors PartyType =
  Map.fromFoldable
    [ (Tuple "PK" [ DefaultString "pubKey" ])
    , (Tuple "Role" [ DefaultString "token" ])
    ]

allMarloweConstructors :: Map String (Array Argument)
allMarloweConstructors = foldMap getMarloweConstructors allMarloweTypes

allMarloweConstructorNames :: Map String MarloweType
allMarloweConstructorNames = foldMap f allMarloweTypes
  where
  f :: MarloweType -> Map String MarloweType
  f marloweType' =
    let
      constructors = Map.keys $ getMarloweConstructors marloweType'

      kvs :: Array (Tuple String MarloweType)
      kvs = Set.toUnfoldable $ Set.map (\constructor -> Tuple constructor marloweType') constructors
    in
      Map.fromFoldable kvs

-- Based on a String representation of a constructor get the MarloweType
-- "Close" -> ContractType
-- "PK" -> PartyType
getMarloweTypeFromConstructor :: String -> Maybe MarloweType
getMarloweTypeFromConstructor constructor =
  let
    f t = Set.member constructor (Map.keys (getMarloweConstructors t))
  in
    Array.find f allMarloweTypes

-- | Return a constructor name if there is exactly one constructor for a type
getConstructorFromMarloweType :: MarloweType -> Maybe String
getConstructorFromMarloweType t = case Set.toUnfoldable $ Map.keys (getMarloweConstructors t) of
  [ constructorName ] -> Just constructorName
  _ -> Nothing

-- | Creates a String consisting of the data constructor name followed by argument holes
--   e.g. "When [ ?case_10 ] ?timeout_11 ?contract_12"
constructMarloweType :: String -> MarloweHole -> Map String (Array Argument) -> String
constructMarloweType constructorName (MarloweHole { range: { startColumn, startLineNumber } }) m = case Map.lookup constructorName m of
  Nothing -> ""
  Just [] -> constructorName
  Just vs -> parens startLineNumber startColumn $ constructorName <> " " <> intercalate " " (map showArgument vs)
  where
  showArgument EmptyArrayArg = "[]"

  showArgument (ArrayArg arg) = "[ ?" <> arg <> " ]"

  showArgument (DataArg arg) = "?" <> mkArgName arg

  showArgument (NamedDataArg arg) = "?" <> arg

  showArgument (DataArgIndexed i arg) = "?" <> mkArgName arg <> show i

  showArgument (DefaultString arg) = "\"" <> arg <> "\""

  showArgument (DefaultNumber arg) = show arg

  showArgument (DefaultRational arg) = show arg

  showArgument NewtypeArg = ""

  showArgument (GenArg marloweType) = case getConstructorFromMarloweType marloweType of
    Nothing -> "?hole"
    Just name ->
      let
        newArgs = getMarloweConstructors marloweType

        hole = MarloweHole { name, marloweType, range: zero }
      in
        constructMarloweType name hole newArgs

  parens 1 1 text = text

  parens _ _ text = "(" <> text <> ")"

type Range
  = { startLineNumber :: Int
    , startColumn :: Int
    , endLineNumber :: Int
    , endColumn :: Int
    }

-- We need to compare the fields in the correct order
compareRange :: Range -> Range -> Ordering
compareRange =
  compare `on` _.startColumn
    <> compare `on` _.startLineNumber
    <> compare `on` _.endLineNumber
    <> compare `on` _.endColumn

data Term a
  = Term a Range
  | Hole String (Proxy a) Range

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

mkHole :: forall a. String -> Range -> Term a
mkHole name range = Hole name Proxy range

mkDefaultTerm :: forall a. a -> Term a
mkDefaultTerm a = Term a zero

class HasMarloweHoles a where
  getHoles :: a -> Holes -> Holes

type ContractData
  = { parties :: Set Party
    , tokens :: Set Token
    }

_parties :: forall s. Lens' { parties :: Set Party | s } (Set Party)
_parties = prop (SProxy :: SProxy "parties")

_tokens :: forall s. Lens' { tokens :: Set Token | s } (Set Token)
_tokens = prop (SProxy :: SProxy "tokens")

class HasContractData a where
  gatherContractData :: a -> ContractData -> ContractData

instance termHasMarloweHoles :: (IsMarloweType a, HasMarloweHoles a) => HasMarloweHoles (Term a) where
  getHoles (Term a _) m = getHoles a m
  getHoles h m = insertHole h m

instance termHasContractData :: HasContractData a => HasContractData (Term a) where
  gatherContractData (Term a _) s = gatherContractData a s
  gatherContractData _ s = s

instance termFromTerm :: FromTerm a b => FromTerm (Term a) b where
  fromTerm (Term a _) = fromTerm a
  fromTerm _ = Nothing

getRange :: forall a. Term a -> Range
getRange (Term _ range) = range

getRange (Hole _ _ range) = range

-- A TermWrapper is like a Term but doesn't have a Hole constructor
data TermWrapper a
  = TermWrapper a Range

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

instance termWrapperHasContractData :: HasContractData a => HasContractData (TermWrapper a) where
  gatherContractData (TermWrapper a _) s = gatherContractData a s

mkDefaultTermWrapper :: forall a. a -> TermWrapper a
mkDefaultTermWrapper a = TermWrapper a zero

-- special case
instance fromTermRational :: FromTerm Rational Rational where
  fromTerm = pure

-- a concrete type for holes only
newtype MarloweHole
  = MarloweHole
  { name :: String
  , marloweType :: MarloweType
  , range :: Range
  }

derive instance genericMarloweHole :: Generic MarloweHole _

derive instance eqMarloweHole :: Eq MarloweHole

instance ordMarloweHole :: Ord MarloweHole where
  compare (MarloweHole { range: a }) (MarloweHole { range: b }) = compareRange a b

instance showMarloweHole :: Show MarloweHole where
  show = genericShow

derive newtype instance encodeMarloweHole :: Encode MarloweHole

derive newtype instance decodeMarloweHole :: Decode MarloweHole

class IsMarloweType a where
  marloweType :: Proxy a -> MarloweType

marloweHoleToSuggestionText :: Boolean -> MarloweHole -> String -> String
marloweHoleToSuggestionText stripParens firstHole@(MarloweHole { marloweType }) constructorName =
  let
    m = getMarloweConstructors marloweType

    fullInsertText = constructMarloweType constructorName firstHole m
  in
    if stripParens then
      Text.stripParens fullInsertText
    else
      fullInsertText

marloweHoleToSuggestion :: String -> Boolean -> IRange -> MarloweHole -> String -> CompletionItem
marloweHoleToSuggestion original stripParens range marloweHole@(MarloweHole { marloweType }) constructorName =
  let
    kind = completionItemKind "Constructor"

    insertText = marloweHoleToSuggestionText stripParens marloweHole constructorName

    preselect = contains (Pattern original) constructorName

    -- Weirdly, the item that has sortText equal to the word you typed is shown at the _bottom_ of the list so
    -- since we want it to be at the top (so if you typed `W` you would have `When` at the top) we make sure it
    -- is the _only_ one that doesn't have the 'correct' sortText.
    -- The weirdest thing happens here, if you use mempty instead of "*" then Debug.trace shows constructorName
    -- and this causes the ordering in Monaco not to work, it's crazy that Debug.trace seems to display the wrong thing
    sortText = if preselect then "*" else original
  in
    { label: constructorName
    , kind
    , range
    , insertText
    , filterText: original
    , sortText
    , preselect
    }

holeSuggestions :: String -> Boolean -> IRange -> MarloweHole -> Array CompletionItem
holeSuggestions original stripParens range marloweHole@(MarloweHole { name, marloweType }) =
  let
    marloweHoles = getMarloweConstructors marloweType
  in
    map (marloweHoleToSuggestion original stripParens range marloweHole) $ Set.toUnfoldable $ Map.keys marloweHoles

-- a Monoid for collecting Holes
newtype Holes
  = Holes (Map String (Set MarloweHole))

derive instance genericHoles :: Generic Holes _

derive instance newtypeHoles :: Newtype Holes _

derive newtype instance eqHoles :: Eq Holes

derive newtype instance ordHoles :: Ord Holes

derive newtype instance showHoles :: Show Holes

instance semigroupHoles :: Semigroup Holes where
  append (Holes a) (Holes b) = Holes (Map.unionWith append a b)

derive newtype instance monoidHoles :: Monoid Holes

instance encodeHoles :: Encode Holes where
  encode (Holes ps) = encode ps

instance decodeHoles :: Decode Holes where
  decode f = Holes <$> decode f

isEmpty :: Holes -> Boolean
isEmpty = Map.isEmpty <<< unwrap

insertHole :: forall a. IsMarloweType a => Term a -> Holes -> Holes
insertHole (Term _ _) m = m

insertHole (Hole name proxy range) (Holes m) = Holes $ Map.alter f name m
  where
  marloweHole = MarloweHole { name, marloweType: (marloweType proxy), range }

  f v = Just (Set.insert marloweHole $ fromMaybe mempty v)

instance arrayHasMarloweHoles :: HasMarloweHoles a => HasMarloweHoles (Array a) where
  getHoles as m = foldMap (\a -> getHoles a m) as

instance arrayHasContractData :: HasContractData a => HasContractData (Array a) where
  gatherContractData as s = foldMap (\a -> gatherContractData a s) as

data Bound
  = Bound BigInteger BigInteger

derive instance genericBound :: Generic Bound _

derive instance eqBound :: Eq Bound

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

derive instance eqParty :: Eq Party

derive instance ordParty :: Ord Party

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

instance partyHasContractData :: HasContractData Party where
  gatherContractData party s = over _parties (Set.insert party) s

type AccountId
  = Term Party

data Token
  = Token String String

derive instance genericToken :: Generic Token _

derive instance eqToken :: Eq Token

derive instance ordToken :: Ord Token

instance showToken :: Show Token where
  show = genericShow

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

instance tokenHasContractData :: HasContractData Token where
  gatherContractData token s = over _tokens (Set.insert token) s

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

instance choiceIdHasContractData :: HasContractData ChoiceId where
  gatherContractData (ChoiceId _ party) s = gatherContractData party s

data Action
  = Deposit AccountId (Term Party) (Term Token) (Term Value)
  | Choice ChoiceId (Array (Term Bound))
  | Notify (Term Observation)

derive instance genericAction :: Generic Action _

derive instance eqAction :: Eq Action

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

instance actionHasContractData :: HasContractData Action where
  gatherContractData (Deposit accountId party token value) s = gatherContractData accountId s <> gatherContractData party s <> gatherContractData value s <> gatherContractData token s
  gatherContractData (Choice choiceId _) s = gatherContractData choiceId s
  gatherContractData (Notify obs) s = gatherContractData obs s

data Payee
  = Account AccountId
  | Party (Term Party)

derive instance genericPayee :: Generic Payee _

derive instance eqPayee :: Eq Payee

derive instance ordPayee :: Ord Payee

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

instance payeeHasContractData :: HasContractData Payee where
  gatherContractData (Account accountId) s = gatherContractData accountId s
  gatherContractData (Party party) s = gatherContractData party s

data Case
  = Case (Term Action) (Term Contract)

derive instance genericCase :: Generic Case _

derive instance eqCase :: Eq Case

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

instance caseHasContractData :: HasContractData Case where
  gatherContractData (Case action contract) s = gatherContractData action s <> gatherContractData contract s

data Value
  = AvailableMoney AccountId (Term Token)
  | Constant BigInteger
  | NegValue (Term Value)
  | AddValue (Term Value) (Term Value)
  | SubValue (Term Value) (Term Value)
  | MulValue (Term Value) (Term Value)
  | Scale (TermWrapper Rational) (Term Value)
  | ChoiceValue ChoiceId
  | SlotIntervalStart
  | SlotIntervalEnd
  | UseValue (TermWrapper ValueId)
  | Cond (Term Observation) (Term Value) (Term Value)

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
  fromTerm (MulValue a b) = S.MulValue <$> fromTerm a <*> fromTerm b
  fromTerm (Scale a b) = S.Scale <$> fromTerm a <*> fromTerm b
  fromTerm (ChoiceValue a) = S.ChoiceValue <$> fromTerm a
  fromTerm SlotIntervalStart = pure S.SlotIntervalStart
  fromTerm SlotIntervalEnd = pure S.SlotIntervalEnd
  fromTerm (UseValue a) = S.UseValue <$> fromTerm a
  fromTerm (Cond c a b) = S.Cond <$> fromTerm c <*> fromTerm a <*> fromTerm b

instance valueIsMarloweType :: IsMarloweType Value where
  marloweType _ = ValueType

instance valueHasContractData :: HasContractData Value where
  gatherContractData (AvailableMoney a token) s = gatherContractData a s <> gatherContractData token s
  gatherContractData (NegValue a) s = gatherContractData a s
  gatherContractData (AddValue a b) s = gatherContractData a s <> gatherContractData b s
  gatherContractData (SubValue a b) s = gatherContractData a s <> gatherContractData b s
  gatherContractData (MulValue a b) s = gatherContractData a s <> gatherContractData b s
  gatherContractData (Scale _ a) s = gatherContractData a s
  gatherContractData (ChoiceValue a) s = gatherContractData a s
  gatherContractData (Cond c a b) s = gatherContractData c s <> gatherContractData a s <> gatherContractData b s
  gatherContractData _ s = s

data Observation
  = AndObs (Term Observation) (Term Observation)
  | OrObs (Term Observation) (Term Observation)
  | NotObs (Term Observation)
  | ChoseSomething ChoiceId
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

instance observationHasContractData :: HasContractData Observation where
  gatherContractData (AndObs a b) s = gatherContractData a s <> gatherContractData b s
  gatherContractData (OrObs a b) s = gatherContractData a s <> gatherContractData b s
  gatherContractData (NotObs a) s = gatherContractData a s
  gatherContractData (ChoseSomething a) s = gatherContractData a s
  gatherContractData (ValueGE a b) s = gatherContractData a s <> gatherContractData b s
  gatherContractData (ValueGT a b) s = gatherContractData a s <> gatherContractData b s
  gatherContractData (ValueLT a b) s = gatherContractData a s <> gatherContractData b s
  gatherContractData (ValueLE a b) s = gatherContractData a s <> gatherContractData b s
  gatherContractData (ValueEQ a b) s = gatherContractData a s <> gatherContractData b s
  gatherContractData _ s = s

data Contract
  = Close
  | Pay AccountId (Term Payee) (Term Token) (Term Value) (Term Contract)
  | If (Term Observation) (Term Contract) (Term Contract)
  | When (Array (Term Case)) (TermWrapper Slot) (Term Contract)
  | Let (TermWrapper ValueId) (Term Value) (Term Contract)
  | Assert (Term Observation) (Term Contract)

derive instance genericContract :: Generic Contract _

derive instance eqContract :: Eq Contract

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
  fromTerm (When as (TermWrapper b _) c) = S.When <$> (traverse fromTerm as) <*> pure b <*> fromTerm c
  fromTerm (Let a b c) = S.Let <$> fromTerm a <*> fromTerm b <*> fromTerm c
  fromTerm (Assert a b) = S.Assert <$> fromTerm a <*> fromTerm b

instance contractIsMarloweType :: IsMarloweType Contract where
  marloweType _ = ContractType

instance contractHasContractData :: HasContractData Contract where
  gatherContractData Close s = s
  gatherContractData (Pay a b c d e) s = gatherContractData a s <> gatherContractData b s <> gatherContractData c s <> gatherContractData d s <> gatherContractData e s
  gatherContractData (If a b c) s = gatherContractData a s <> gatherContractData b s <> gatherContractData c s
  gatherContractData (When as _ b) s = gatherContractData as s <> gatherContractData b s
  gatherContractData (Let _ a b) s = gatherContractData a s <> gatherContractData b s
  gatherContractData (Assert a b) s = gatherContractData a s <> gatherContractData b s

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
