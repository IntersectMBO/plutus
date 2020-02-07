module Marlowe.Holes where

import Prelude
import Data.Array (foldMap, foldl, mapWithIndex, (:))
import Data.BigInteger (BigInteger)
import Data.Foldable (intercalate)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Function (on)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Eq (genericEq)
import Data.Generic.Rep.Show (genericShow)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (length)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Marlowe.Pretty (class Pretty, genericPretty, prettyFragment)
import Marlowe.Semantics (ChosenNum, Money, PubKey, Slot, Timeout, TokenName)
import Marlowe.Semantics as S
import Text.Parsing.Parser.Basic (replaceInPosition)
import Text.Parsing.Parser.Pos (Position(..))
import Text.PrettyPrint.Leijen (appendWithSoftbreak)
import Text.PrettyPrint.Leijen as Leijen
import Type.Proxy (Proxy)

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
  | BoundType
  | TokenType
  | PartyType

derive instance eqMarloweType :: Eq MarloweType

data Argument
  = ArrayArg String
  | DataArg String
  | NewtypeArg

getMarloweConstructors :: MarloweType -> Map String (Array Argument)
getMarloweConstructors StringType = Map.singleton "String" [ NewtypeArg ]

getMarloweConstructors BigIntegerType = Map.singleton "Integer" [ NewtypeArg ]

getMarloweConstructors SlotType = Map.singleton "Integer" [ NewtypeArg ]

getMarloweConstructors AccountIdType = Map.singleton "AccountId" [ DataArg "accNumber", DataArg "accHolder" ]

getMarloweConstructors ChoiceIdType = Map.singleton "ChoiceId" [ DataArg "choiceNumber", DataArg "choiceOwner" ]

getMarloweConstructors ValueIdType = Map.singleton "ValueId" [ NewtypeArg ]

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
    , (Tuple "Constant" [ DataArg "amount" ])
    , (Tuple "NegValue" [ DataArg "value" ])
    , (Tuple "AddValue" [ DataArg "value", DataArg "value" ])
    , (Tuple "SubValue" [ DataArg "value", DataArg "value" ])
    , (Tuple "ChoiceValue" [ DataArg "choiceId", DataArg "value" ])
    , (Tuple "SlotIntervalStart" [])
    , (Tuple "SlotIntervalEnd" [])
    , (Tuple "UseValue" [ DataArg "valueId" ])
    ]

getMarloweConstructors InputType =
  Map.fromFoldable
    [ (Tuple "IDeposit" [ DataArg "accountId", DataArg "party", DataArg "token", DataArg "money" ])
    , (Tuple "IChoice" [ DataArg "choiceId", DataArg "choiceNum" ])
    , (Tuple "INotify" [])
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
    , (Tuple "When" [ ArrayArg "case", DataArg "timeout", DataArg "contract" ])
    , (Tuple "Let" [ DataArg "valueId", DataArg "value", DataArg "contract" ])
    ]

getMarloweConstructors BoundType = Map.singleton "Bound" [ DataArg "from", DataArg "to" ]

getMarloweConstructors TokenType = Map.singleton "Token" [ DataArg "currency", DataArg "token" ]

getMarloweConstructors PartyType =
  Map.fromFoldable
    [ (Tuple "PK" [ DataArg "pubKey" ])
    , (Tuple "Role" [ DataArg "token" ])
    ]

constructMarloweType :: String -> MarloweHole -> Map String (Array Argument) -> String
constructMarloweType constructorName (MarloweHole { name, marloweType, start }) m = case Map.lookup constructorName m of
  Nothing -> ""
  Just [] -> constructorName
  Just vs ->
    let
      Position { line, column } = start
    in
      "(" <> constructorName <> " " <> intercalate " " (mapWithIndex (showArgument line column) vs) <> ")"
  where
  showArgument line column i (ArrayArg arg) = "[ ?" <> arg <> "_" <> show line <> "_" <> show (column + i) <> " ]"

  showArgument line column i (DataArg arg) = "?" <> arg <> "_" <> show line <> "_" <> show (column + i)

  showArgument _ _ _ NewtypeArg = ""

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

derive instance eqMarloweHole :: Eq MarloweHole

instance ordMarloweHole :: Ord MarloweHole where
  compare (MarloweHole { start: (Position a) }) (MarloweHole { start: (Position b) }) = (compare `on` _.line <> compare `on` _.column) a b

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

  f v = Just (marloweHole : fromMaybe [] v)

class HasMarloweHoles a where
  getHoles :: Holes -> a -> Holes

instance termHasMarloweHoles :: (IsMarloweType a, HasMarloweHoles a) => HasMarloweHoles (Term a) where
  getHoles m (Term a) = getHoles m a
  getHoles m h = insertHole m h

instance arrayHasMarloweHoles :: HasMarloweHoles a => HasMarloweHoles (Array a) where
  getHoles m as = foldMap (getHoles m) as

-- Parsable versions of the Marlowe types
data Bound
  = Bound (Term BigInteger) (Term BigInteger)

derive instance genericBound :: Generic Bound _

instance showBound :: Show Bound where
  show v = genericShow v

instance prettyBound :: Pretty Bound where
  prettyFragment a = Leijen.text $ show a

instance boundFromTerm :: FromTerm Bound S.Bound where
  fromTerm (Bound a b) = S.Bound <$> termToValue a <*> termToValue b

instance boundIsMarloweType :: IsMarloweType Bound where
  marloweType _ = BoundType

instance boundHasMarloweHoles :: HasMarloweHoles Bound where
  getHoles m (Bound a b) = insertHole m a <> insertHole m b

data Party
  = PK (Term PubKey)
  | Role (Term TokenName)

derive instance genericParty :: Generic Party _

instance showParty :: Show Party where
  show v = genericShow v

instance prettyParty :: Pretty Party where
  prettyFragment a = Leijen.text (show a)

instance partyFromTerm :: FromTerm Party S.Party where
  fromTerm (PK (Term b)) = pure $ S.PK b
  fromTerm (Role (Term b)) = pure $ S.Role b
  fromTerm _ = Nothing

instance partyIsMarloweType :: IsMarloweType Party where
  marloweType _ = PartyType

instance partyHasMarloweHoles :: HasMarloweHoles Party where
  getHoles m (PK a) = insertHole m a
  getHoles m (Role a) = insertHole m a

data AccountId
  = AccountId (Term BigInteger) (Term Party)

derive instance genericAccountId :: Generic AccountId _

instance showAccountId :: Show AccountId where
  show v = genericShow v

instance prettyAccountId :: Pretty AccountId where
  prettyFragment a = Leijen.text (show a)

instance accountIdFromTerm :: FromTerm AccountId S.AccountId where
  fromTerm (AccountId (Term b) (Term c)) = S.AccountId <$> pure b <*> fromTerm c
  fromTerm _ = Nothing

instance accountIdIsMarloweType :: IsMarloweType AccountId where
  marloweType _ = AccountIdType

instance accountIdHasMarloweHoles :: HasMarloweHoles AccountId where
  getHoles m (AccountId a b) = insertHole m a <> insertHole m b

data Token
  = Token (Term String) (Term String)

derive instance genericToken :: Generic Token _

instance showToken :: Show Token where
  show tok = genericShow tok

instance prettyToken :: Pretty Token where
  prettyFragment a = Leijen.text (show a)

instance tokenFromTerm :: FromTerm Token S.Token where
  fromTerm (Token (Term b) (Term c)) = pure $ S.Token b c
  fromTerm _ = Nothing

instance tokenIsMarloweType :: IsMarloweType Token where
  marloweType _ = TokenType

instance tokenHasMarloweHoles :: HasMarloweHoles Token where
  getHoles m (Token a b) = insertHole m a <> insertHole m b

data ChoiceId
  = ChoiceId (Term String) (Term Party)

derive instance genericChoiceId :: Generic ChoiceId _

instance showChoiceId :: Show ChoiceId where
  show v = genericShow v

instance prettyChoiceId :: Pretty ChoiceId where
  prettyFragment a = Leijen.text (show a)

instance choiceIdFromTerm :: FromTerm ChoiceId S.ChoiceId where
  fromTerm (ChoiceId (Term a) (Term b)) = S.ChoiceId <$> pure a <*> fromTerm b
  fromTerm _ = Nothing

instance choiceIdIsMarloweType :: IsMarloweType ChoiceId where
  marloweType _ = ChoiceIdType

instance choiceIdHasMarloweHoles :: HasMarloweHoles ChoiceId where
  getHoles m (ChoiceId a b) = insertHole m a <> insertHole m b

data Action
  = Deposit (Term AccountId) (Term Party) (Term Token) (Term Value)
  | Choice (Term ChoiceId) (Array (Term Bound))
  | Notify (Term Observation)

derive instance genericAction :: Generic Action _

instance showAction :: Show Action where
  show v = genericShow v

instance prettyAction :: Pretty Action where
  prettyFragment a = Leijen.text (show a)

instance actionFromTerm :: FromTerm Action S.Action where
  fromTerm (Deposit a b c d) = S.Deposit <$> fromTerm a <*> fromTerm b <*> fromTerm c <*> fromTerm d
  fromTerm (Choice a b) = S.Choice <$> fromTerm a <*> (traverse fromTerm b)
  fromTerm (Notify a) = S.Notify <$> fromTerm a

instance actionMarloweType :: IsMarloweType Action where
  marloweType _ = ActionType

instance actionHasMarloweHoles :: HasMarloweHoles Action where
  getHoles m (Deposit a b c d) = getHoles m a <> insertHole m b <> getHoles m c <> getHoles m d
  getHoles m (Choice a bs) = getHoles m a <> getHoles m bs
  getHoles m (Notify a) = getHoles m a

data Payee
  = Account (Term AccountId)
  | Party (Term Party)

derive instance genericPayee :: Generic Payee _

instance showPayee :: Show Payee where
  show v = genericShow v

instance prettyPayee :: Pretty Payee where
  prettyFragment a = genericPretty a

instance payeeFromTerm :: FromTerm Payee S.Payee where
  fromTerm (Account a) = S.Account <$> fromTerm a
  fromTerm (Party (Term a)) = S.Party <$> fromTerm a
  fromTerm _ = Nothing

instance payeeMarloweType :: IsMarloweType Payee where
  marloweType _ = PayeeType

instance payeeHasMarloweHoles :: HasMarloweHoles Payee where
  getHoles m (Account a) = getHoles m a
  getHoles m (Party a) = insertHole m a

data Case
  = Case (Term Action) (Term Contract)

derive instance genericCase :: Generic Case _

instance showCase :: Show Case where
  show v = genericShow v

-- FIXME: pretty printing is a disaster and slooooowwwww
instance prettyCase :: Pretty Case where
  prettyFragment (Case action' contract') = appendWithSoftbreak (Leijen.text "Case " <> prettyFragment action' <> Leijen.text " ") (prettyFragment contract')

instance caseFromTerm :: FromTerm Case S.Case where
  fromTerm (Case a b) = S.Case <$> fromTerm a <*> fromTerm b

instance caseMarloweType :: IsMarloweType Case where
  marloweType _ = CaseType

instance caseHasMarloweHoles :: HasMarloweHoles Case where
  getHoles m (Case a b) = getHoles m a <> getHoles m b

data Value
  = AvailableMoney (Term AccountId) (Term Token)
  | Constant (Term BigInteger)
  | NegValue (Term Value)
  | AddValue (Term Value) (Term Value)
  | SubValue (Term Value) (Term Value)
  | ChoiceValue (Term ChoiceId) (Term Value)
  | SlotIntervalStart
  | SlotIntervalEnd
  | UseValue (Term ValueId)

derive instance genericValue :: Generic Value _

instance showValue :: Show Value where
  show v = genericShow v

instance prettyValue :: Pretty Value where
  prettyFragment a = genericPretty a

instance valueFromTerm :: FromTerm Value S.Value where
  fromTerm (AvailableMoney a b) = S.AvailableMoney <$> fromTerm a <*> fromTerm b
  fromTerm (Constant a) = S.Constant <$> termToValue a
  fromTerm (NegValue a) = S.NegValue <$> fromTerm a
  fromTerm (AddValue a b) = S.AddValue <$> fromTerm a <*> fromTerm b
  fromTerm (SubValue a b) = S.SubValue <$> fromTerm a <*> fromTerm b
  fromTerm (ChoiceValue a b) = S.ChoiceValue <$> fromTerm a <*> fromTerm b
  fromTerm SlotIntervalStart = pure S.SlotIntervalStart
  fromTerm SlotIntervalEnd = pure S.SlotIntervalEnd
  fromTerm (UseValue a) = S.UseValue <$> fromTerm a

instance valueIsMarloweType :: IsMarloweType Value where
  marloweType _ = ValueType

instance valueHasMarloweHoles :: HasMarloweHoles Value where
  getHoles m (AvailableMoney a b) = getHoles m a <> getHoles m b
  getHoles m (Constant a) = insertHole m a
  getHoles m (NegValue a) = getHoles m a
  getHoles m (AddValue a b) = getHoles m a <> getHoles m b
  getHoles m (SubValue a b) = getHoles m a <> getHoles m b
  getHoles m (ChoiceValue a b) = getHoles m a <> getHoles m b
  getHoles m SlotIntervalStart = mempty
  getHoles m SlotIntervalEnd = mempty
  getHoles m (UseValue a) = getHoles m a

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

instance showObservation :: Show Observation where
  show v = genericShow v

instance prettyObservation :: Pretty Observation where
  prettyFragment a = genericPretty a

instance fromTermTerm :: FromTerm a b => FromTerm (Term a) b where
  fromTerm (Term a) = fromTerm a
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

instance observationHasMarloweHoles :: HasMarloweHoles Observation where
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

data Contract
  = Close
  | Pay (Term AccountId) (Term Payee) (Term Token) (Term Value) (Term Contract)
  | If (Term Observation) (Term Contract) (Term Contract)
  | When (Array (Term Case)) (Term Timeout) (Term Contract)
  | Let (Term ValueId) (Term Value) (Term Contract)

derive instance genericContract :: Generic Contract _

instance showContract :: Show Contract where
  show v = genericShow v

instance prettyContract :: Pretty Contract where
  prettyFragment a = genericPretty a

instance contractFromTerm :: FromTerm Contract S.Contract where
  fromTerm Close = pure S.Close
  fromTerm (Pay a b c d e) = S.Pay <$> fromTerm a <*> fromTerm b <*> fromTerm c <*> fromTerm d <*> fromTerm e
  fromTerm (If a b c) = S.If <$> fromTerm a <*> fromTerm b <*> fromTerm c
  fromTerm (When as b c) = S.When <$> (traverse fromTerm as) <*> termToValue b <*> fromTerm c
  fromTerm (Let a b c) = S.Let <$> fromTerm a <*> fromTerm b <*> fromTerm c

instance contractIsMarloweType :: IsMarloweType Contract where
  marloweType _ = ContractType

instance contractHasMarloweHoles :: HasMarloweHoles Contract where
  getHoles m Close = mempty
  getHoles m (Pay a b c d e) = getHoles m a <> getHoles m b <> getHoles m c <> getHoles m d <> getHoles m e
  getHoles m (If a b c) = getHoles m a <> getHoles m b <> getHoles m c
  getHoles m (When as b c) = getHoles m as <> insertHole m b <> getHoles m c
  getHoles m (Let a b c) = getHoles m a <> getHoles m b <> getHoles m c

newtype ValueId
  = ValueId String

derive instance genericValueId :: Generic ValueId _

instance showValueId :: Show ValueId where
  show (ValueId valueId') = show valueId'

instance prettyValueId :: Pretty ValueId where
  prettyFragment a = Leijen.text (show a)

instance valueIdFromTerm :: FromTerm ValueId S.ValueId where
  fromTerm (ValueId a) = pure $ S.ValueId a

instance valueIdIsMarloweType :: IsMarloweType ValueId where
  marloweType _ = ValueIdType

instance valueIdHasMarloweHoles :: HasMarloweHoles ValueId where
  getHoles m _ = m

termToValue :: forall a. Term a -> Maybe a
termToValue (Term a) = Just a

termToValue _ = Nothing

class FromTerm a b where
  fromTerm :: a -> Maybe b

instance slotMarloweType :: IsMarloweType Slot where
  marloweType _ = SlotType

-- Replace all holes of a certain name with the value
replaceInPositions :: String -> MarloweHole -> Array MarloweHole -> String -> String
replaceInPositions constructor firstHole@(MarloweHole { marloweType }) holes currentContract =
  let
    offset (Position { line, column }) x = Position { line, column: column + x }

    lengthOfReplacement value (Position { column: start }) (Position { column: end }) = (length value) - (end - start)

    getLine (Position { line }) = line

    m = getMarloweConstructors marloweType

    holeString = constructMarloweType constructor firstHole m

    (_ /\ _ /\ final) =
      ( foldl
          ( \(currLength /\ currLineNumber /\ currString) hole@(MarloweHole { name, marloweType, start, end }) ->
              let
                thisLine = getLine start

                thisLength = currLength + (lengthOfReplacement holeString start end)
              in
                if currLineNumber == thisLine then
                  ( thisLength
                      /\ thisLine
                      /\ (replaceInPosition (offset start thisLength) (offset end thisLength) holeString currString)
                  )
                else
                  ( 0
                      /\ thisLine
                      /\ (replaceInPosition start end holeString currString)
                  )
          )
          (0 /\ 0 /\ currentContract)
          holes
      )
  in
    final
