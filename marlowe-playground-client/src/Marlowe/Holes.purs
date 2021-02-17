module Marlowe.Holes where

import Prelude
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
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, unwrap)
import Data.Set (Set)
import Data.Set as Set
import Data.String (splitAt, toLower)
import Data.String.CodeUnits (dropRight)
import Data.Symbol (SProxy(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect.Exception.Unsafe (unsafeThrow)
import Foreign.Generic (class Decode, class Encode, defaultOptions, genericDecode, genericEncode)
import Marlowe.Extended as EM
import Marlowe.Semantics (PubKey, Rational(..), TokenName, CurrencySymbol)
import Marlowe.Semantics as S
import Monaco (IRange)
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
  | TimeoutType

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

readMarloweType "TimeoutType" = Just TimeoutType

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

-- | TermGenerator is a decorator for Array Argument. Array Argument is used, among other things, for generating
-- | terms from holes. But, by default, it includes the constructor name, e.g: "Slot ?slotNumber"
-- | In the case of Slot, we just want to generate the argument, i.e: "0", not "Slot 0",
-- | that is what SimpleArgument does. See implementation of `constructMarloweType` function.
data TermGenerator
  = ArgumentArray (Array Argument)
  | SimpleArgument Argument

getMarloweConstructors :: MarloweType -> Map String TermGenerator
getMarloweConstructors ChoiceIdType = Map.singleton "ChoiceId" $ ArgumentArray [ DefaultString "choiceNumber", DataArg PartyType ]

getMarloweConstructors ValueIdType = mempty

getMarloweConstructors ActionType =
  Map.fromFoldable
    [ (Tuple "Deposit" $ ArgumentArray [ DataArg PartyType, NamedDataArg "from_party", DataArg TokenType, DataArg ValueType ])
    , (Tuple "Choice" $ ArgumentArray [ GenArg ChoiceIdType, ArrayArg "bounds" ])
    , (Tuple "Notify" $ ArgumentArray [ DataArg ObservationType ])
    ]

getMarloweConstructors PayeeType =
  Map.fromFoldable
    [ (Tuple "Account" $ ArgumentArray [ DataArg PartyType ])
    , (Tuple "Party" $ ArgumentArray [ DataArg PartyType ])
    ]

getMarloweConstructors CaseType = Map.singleton "Case" $ ArgumentArray [ DataArg ActionType, DataArg ContractType ]

getMarloweConstructors ValueType =
  Map.fromFoldable
    [ (Tuple "AvailableMoney" $ ArgumentArray [ DataArg PartyType, DataArg TokenType ])
    , (Tuple "Constant" $ ArgumentArray [ DefaultNumber zero ])
    , (Tuple "ConstantParam" $ ArgumentArray [ DefaultString "parameterName" ])
    , (Tuple "NegValue" $ ArgumentArray [ DataArg ValueType ])
    , (Tuple "AddValue" $ ArgumentArray [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "SubValue" $ ArgumentArray [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "MulValue" $ ArgumentArray [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "Scale" $ ArgumentArray [ DefaultRational (Rational one one), DataArg ValueType ])
    , (Tuple "ChoiceValue" $ ArgumentArray [ GenArg ChoiceIdType ])
    , (Tuple "SlotIntervalStart" $ ArgumentArray [])
    , (Tuple "SlotIntervalEnd" $ ArgumentArray [])
    , (Tuple "UseValue" $ ArgumentArray [ DefaultString "valueId" ])
    , (Tuple "Cond" $ ArgumentArray [ DataArg ObservationType, DataArg ValueType, DataArg ValueType ])
    ]

getMarloweConstructors ObservationType =
  Map.fromFoldable
    [ (Tuple "AndObs" $ ArgumentArray [ DataArgIndexed 1 ObservationType, DataArgIndexed 2 ObservationType ])
    , (Tuple "OrObs" $ ArgumentArray [ DataArgIndexed 1 ObservationType, DataArgIndexed 2 ObservationType ])
    , (Tuple "NotObs" $ ArgumentArray [ DataArg ObservationType ])
    , (Tuple "ChoseSomething" $ ArgumentArray [ GenArg ChoiceIdType ])
    , (Tuple "ValueGE" $ ArgumentArray [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "ValueGT" $ ArgumentArray [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "ValueLE" $ ArgumentArray [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "ValueLT" $ ArgumentArray [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "ValueEQ" $ ArgumentArray [ DataArgIndexed 1 ValueType, DataArgIndexed 2 ValueType ])
    , (Tuple "TrueObs" $ ArgumentArray [])
    , (Tuple "FalseObs" $ ArgumentArray [])
    ]

getMarloweConstructors ContractType =
  Map.fromFoldable
    [ (Tuple "Close" $ ArgumentArray [])
    , (Tuple "Pay" $ ArgumentArray [ DataArg PartyType, DataArg PayeeType, DataArg TokenType, DataArg ValueType, DataArg ContractType ])
    , (Tuple "If" $ ArgumentArray [ DataArg ObservationType, DataArgIndexed 1 ContractType, DataArgIndexed 2 ContractType ])
    , (Tuple "When" $ ArgumentArray [ EmptyArrayArg, DataArg TimeoutType, DataArg ContractType ])
    , (Tuple "Let" $ ArgumentArray [ DefaultString "valueId", DataArg ValueType, DataArg ContractType ])
    , (Tuple "Assert" $ ArgumentArray [ DataArg ObservationType, DataArg ContractType ])
    ]

getMarloweConstructors BoundType = Map.singleton "Bound" $ ArgumentArray [ DefaultNumber zero, DefaultNumber zero ]

getMarloweConstructors TokenType = Map.singleton "Token" $ ArgumentArray [ DefaultString "", DefaultString "" ]

getMarloweConstructors PartyType =
  Map.fromFoldable
    [ (Tuple "PK" $ ArgumentArray [ DefaultString "pubKey" ])
    , (Tuple "Role" $ ArgumentArray [ DefaultString "token" ])
    ]

getMarloweConstructors TimeoutType =
  Map.fromFoldable
    [ (Tuple "Slot" $ SimpleArgument $ DefaultNumber zero)
    , (Tuple "SlotParam" $ ArgumentArray [ DefaultString "slotParameterName" ])
    ]

allMarloweConstructors :: Map String TermGenerator
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
constructMarloweType :: String -> MarloweHole -> Map String TermGenerator -> String
constructMarloweType constructorName (MarloweHole { location }) m = case Map.lookup constructorName m of
  Nothing -> ""
  Just (ArgumentArray []) -> constructorName
  Just (ArgumentArray vs) -> parens location $ constructorName <> " " <> intercalate " " (map showArgument vs)
  Just (SimpleArgument vs) -> showArgument vs
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

        hole = MarloweHole { name, marloweType, location: NoLocation }
      in
        constructMarloweType name hole newArgs

  -- This parens helper adds parentesis to the code if the hole is not in the first line and character
  -- position of the editor. This is like this because the parser throws an error if the Contract starts
  -- with a parentesis. But this check is very basic, if the hole is the first part of the code, but has
  -- an extra space before, the quick-fix will create the contract with a parens and make it invalid.
  -- A couple of things that could be investigated in other PR:
  --   * See if this belongs to LinterMarker rather than Marlowe.Holes, as it's relying on the textual
  --     representation of the marker and a Range location.
  --   * See if we can Modify the parser so that a contract starting with parentesis is valid
  --   * Or see if we have another way to detect the first hole that does not depend on being the first
  --     character
  parens (Range { startColumn: 1, startLineNumber: 1, endColumn: _, endLineNumber: _ }) text = text

  parens _ text = "(" <> text <> ")"

data Location
  = Range IRange
  | BlockId String
  -- CHECK THIS: Before this refactor, the Range had an implicit Semiring constraint in multiple places, for
  -- example mkDefaultTermWrapper. The idea was mainly to use a `zero`/`mempty` location. But having a semiring
  -- is probably not what we want for Range or BlockId. For the moment I'm adding a separate constructor
  -- to the location, but perhaps we want to modify the Term constructor to receive a (Maybe Location) instead.
  | NoLocation

derive instance eqLocation :: Eq Location

derive instance genericSession :: Generic Location _

instance encodeSession :: Encode Location where
  encode value = genericEncode defaultOptions value

instance decodeSession :: Decode Location where
  decode value = genericDecode defaultOptions value

-- We need to compare the fields in the correct order
compareRange :: IRange -> IRange -> Ordering
compareRange =
  compare `on` _.startColumn
    <> compare `on` _.startLineNumber
    <> compare `on` _.endLineNumber
    <> compare `on` _.endColumn

-- FIXME: We should check the need for the different Ord's instances we have here.
--        I've traced that all the Term's instances are required because the Linter has a generic
--        compare on the WarningDetail, which is only used as the fallback case of ordWarning.
--        The other use of ordering is in MarloweHole, to be able to insert them in the `Holes` Set.
--        But that is currently using compareLocation and not the Location Ord instance. And it doesn't
--        necesarely need to be based on location, is just a constraint for Set.
instance ordLocation :: Ord Location where
  compare = compareLocation

compareLocation :: Location -> Location -> Ordering
compareLocation (Range a) (Range b) = compareRange a b

-- TODO: Comparing on String does not make too much sense for ordering blocks id's. Once
--       we refactor Blockly to produce Term's directly, we can see if it makes sense to store
--       the id and the depth and compare on depth.
compareLocation (BlockId a) (BlockId b) = compare a b

compareLocation NoLocation NoLocation = EQ

compareLocation NoLocation _ = LT

compareLocation _ NoLocation = GT

compareLocation (BlockId a) (Range b) = unsafeThrow "Invalid comparation of a BlockId and Range (this should not happen)"

compareLocation (Range a) (BlockId b) = unsafeThrow "Invalid comparation of a BlockId and Range (this should not happen)"

data Term a
  = Term a Location
  | Hole String (Proxy a) Location

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

mkHole :: forall a. String -> Location -> Term a
mkHole name range = Hole name Proxy range

mkDefaultTerm :: forall a. a -> Term a
mkDefaultTerm a = Term a NoLocation

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

getLocation :: forall a. Term a -> Location
getLocation (Term _ location) = location

getLocation (Hole _ _ location) = location

-- A TermWrapper is like a Term but doesn't have a Hole constructor
data TermWrapper a
  = TermWrapper a Location

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
mkDefaultTermWrapper a = TermWrapper a NoLocation

-- special case
instance fromTermRational :: FromTerm Rational Rational where
  fromTerm = pure

-- a concrete type for holes only
newtype MarloweHole
  = MarloweHole
  { name :: String
  , marloweType :: MarloweType
  , location :: Location
  }

derive instance genericMarloweHole :: Generic MarloweHole _

derive instance eqMarloweHole :: Eq MarloweHole

instance ordMarloweHole :: Ord MarloweHole where
  compare (MarloweHole { location: a }) (MarloweHole { location: b }) = compareLocation a b

class IsMarloweType a where
  marloweType :: Proxy a -> MarloweType

-- a Monoid for collecting Holes
newtype Holes
  = Holes (Map String (Set MarloweHole))

derive instance genericHoles :: Generic Holes _

derive instance newtypeHoles :: Newtype Holes _

derive newtype instance eqHoles :: Eq Holes

derive newtype instance ordHoles :: Ord Holes

instance semigroupHoles :: Semigroup Holes where
  append (Holes a) (Holes b) = Holes (Map.unionWith append a b)

derive newtype instance monoidHoles :: Monoid Holes

isEmpty :: Holes -> Boolean
isEmpty = Map.isEmpty <<< unwrap

insertHole :: forall a. IsMarloweType a => Term a -> Holes -> Holes
insertHole (Term _ _) m = m

insertHole (Hole name proxy location) (Holes m) = Holes $ Map.alter f name m
  where
  marloweHole = MarloweHole { name, marloweType: (marloweType proxy), location }

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

data Timeout
  = Slot BigInteger
  | SlotParam String

derive instance genericTimeout :: Generic Timeout _

derive instance eqTimeout :: Eq Timeout

derive instance ordTimeout :: Ord Timeout

instance showTimeout :: Show Timeout where
  show (Slot x) = show x
  show v = genericShow v

instance prettyTimeout :: Pretty Timeout where
  pretty (Slot x) = pretty x
  pretty (SlotParam x) = genericPretty (SlotParam x)

instance hasArgsTimeout :: Args Timeout where
  hasArgs (Slot _) = false
  hasArgs x = genericHasArgs x
  hasNestedArgs (Slot _) = false
  hasNestedArgs x = genericHasNestedArgs x

instance timeoutFromTerm :: FromTerm Timeout EM.Timeout where
  fromTerm (Slot b) = pure $ EM.Slot b
  fromTerm (SlotParam b) = pure $ EM.SlotParam b

instance timeoutIsMarloweType :: IsMarloweType Timeout where
  marloweType _ = TimeoutType

instance timeoutHasMarloweHoles :: HasMarloweHoles Timeout where
  getHoles (Slot a) m = m
  getHoles (SlotParam a) m = m

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
  = Token CurrencySymbol String

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

instance actionFromTerm :: FromTerm Action EM.Action where
  fromTerm (Deposit a b c d) = EM.Deposit <$> fromTerm a <*> fromTerm b <*> fromTerm c <*> fromTerm d
  fromTerm (Choice a b) = EM.Choice <$> fromTerm a <*> (traverse fromTerm b)
  fromTerm (Notify a) = EM.Notify <$> fromTerm a

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

instance payeeFromTerm :: FromTerm Payee EM.Payee where
  fromTerm (Account a) = EM.Account <$> fromTerm a
  fromTerm (Party (Term a _)) = EM.Party <$> fromTerm a
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

instance caseFromTerm :: FromTerm Case EM.Case where
  fromTerm (Case a b) = EM.Case <$> fromTerm a <*> fromTerm b

instance caseMarloweType :: IsMarloweType Case where
  marloweType _ = CaseType

instance caseHasContractData :: HasContractData Case where
  gatherContractData (Case action contract) s = gatherContractData action s <> gatherContractData contract s

data Value
  = AvailableMoney AccountId (Term Token)
  | Constant BigInteger
  | ConstantParam String
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

instance valueFromTerm :: FromTerm Value EM.Value where
  fromTerm (AvailableMoney a b) = EM.AvailableMoney <$> fromTerm a <*> fromTerm b
  fromTerm (Constant a) = pure $ EM.Constant a
  fromTerm (ConstantParam a) = pure $ EM.ConstantParam a
  fromTerm (NegValue a) = EM.NegValue <$> fromTerm a
  fromTerm (AddValue a b) = EM.AddValue <$> fromTerm a <*> fromTerm b
  fromTerm (SubValue a b) = EM.SubValue <$> fromTerm a <*> fromTerm b
  fromTerm (MulValue a b) = EM.MulValue <$> fromTerm a <*> fromTerm b
  fromTerm (Scale a b) = EM.Scale <$> fromTerm a <*> fromTerm b
  fromTerm (ChoiceValue a) = EM.ChoiceValue <$> fromTerm a
  fromTerm SlotIntervalStart = pure EM.SlotIntervalStart
  fromTerm SlotIntervalEnd = pure EM.SlotIntervalEnd
  fromTerm (UseValue a) = EM.UseValue <$> fromTerm a
  fromTerm (Cond c a b) = EM.Cond <$> fromTerm c <*> fromTerm a <*> fromTerm b

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

instance observationFromTerm :: FromTerm Observation EM.Observation where
  fromTerm (AndObs a b) = EM.AndObs <$> fromTerm a <*> fromTerm b
  fromTerm (OrObs a b) = EM.OrObs <$> fromTerm a <*> fromTerm b
  fromTerm (NotObs a) = EM.NotObs <$> fromTerm a
  fromTerm (ChoseSomething a) = EM.ChoseSomething <$> fromTerm a
  fromTerm (ValueGE a b) = EM.ValueGE <$> fromTerm a <*> fromTerm b
  fromTerm (ValueGT a b) = EM.ValueGT <$> fromTerm a <*> fromTerm b
  fromTerm (ValueLT a b) = EM.ValueLT <$> fromTerm a <*> fromTerm b
  fromTerm (ValueLE a b) = EM.ValueLE <$> fromTerm a <*> fromTerm b
  fromTerm (ValueEQ a b) = EM.ValueEQ <$> fromTerm a <*> fromTerm b
  fromTerm TrueObs = pure EM.TrueObs
  fromTerm FalseObs = pure EM.FalseObs

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
  | When (Array (Term Case)) (Term Timeout) (Term Contract)
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

instance contractFromTerm :: FromTerm Contract EM.Contract where
  fromTerm Close = pure EM.Close
  fromTerm (Pay a b c d e) = EM.Pay <$> fromTerm a <*> fromTerm b <*> fromTerm c <*> fromTerm d <*> fromTerm e
  fromTerm (If a b c) = EM.If <$> fromTerm a <*> fromTerm b <*> fromTerm c
  fromTerm (When as b c) = EM.When <$> (traverse fromTerm as) <*> fromTerm b <*> fromTerm c
  fromTerm (Let a b c) = EM.Let <$> fromTerm a <*> fromTerm b <*> fromTerm c
  fromTerm (Assert a b) = EM.Assert <$> fromTerm a <*> fromTerm b

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
