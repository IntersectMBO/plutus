module Marlowe.Linter
  ( lint
  , State(..)
  , Position
  , MaxTimeout
  , Warning(..)
  , _holes
  , _warnings
  , suggestions
  , markers
  , format
  , provideCodeActions
  , getWarningRange
  ) where

import Prelude
import Control.Monad.State as CMS
import Data.Array (fold, foldMap, take)
import Data.Array as Array
import Data.Array.NonEmpty (index)
import Data.BigInteger (BigInteger)
import Data.Either (Either(..), hush)
import Data.Functor (mapFlipped)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Eq (genericEq)
import Data.Generic.Rep.Ord (genericCompare)
import Data.Lens (Lens', modifying, over, to, view, (^.))
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype)
import Data.Ord (abs)
import Data.Set (Set)
import Data.Set as Set
import Data.String (codePointFromChar, fromCodePointArray, length, takeWhile, toCodePointArray)
import Data.String.Regex (match, regex)
import Data.String.Regex.Flags (noFlags)
import Data.Symbol (SProxy(..))
import Data.Traversable (traverse_)
import Data.Tuple.Nested ((/\))
import Marlowe.Holes (Action(..), Argument, Case(..), Contract(..), Holes(..), MarloweHole(..), MarloweType(..), Observation(..), Term(..), Value(..), ValueId, constructMarloweType, getHoles, getMarloweConstructors, getPosition, holeSuggestions, insertHole, readMarloweType)
import Marlowe.Parser (ContractParseError(..), parseContract)
import Marlowe.Semantics (Rational(..), Slot(..), Timeout, emptyState, evalValue, makeEnvironment)
import Marlowe.Semantics as S
import Monaco (CodeAction, CompletionItem, IMarkerData, Uri, IRange, markerSeverity)
import Text.Parsing.StringParser (Pos)
import Text.Pretty (pretty)

type Position
  = { row :: Pos, column :: Pos }

newtype MaxTimeout
  = MaxTimeout Timeout

derive instance newtypeMaxTimeout :: Newtype MaxTimeout _

derive newtype instance eqMaxTimeout :: Eq MaxTimeout

derive newtype instance ordMaxTimeout :: Ord MaxTimeout

instance semigroupMax :: Semigroup MaxTimeout where
  append a b = max a b

instance monoidMaxTimeout :: Monoid MaxTimeout where
  mempty = MaxTimeout zero

data Warning
  = NegativePayment IRange
  | NegativeDeposit IRange
  | TimeoutNotIncreasing IRange
  | UnreachableCase IRange
  | UnreachableContract IRange
  | UndefinedUse IRange
  | ShadowedLet IRange
  | DivisionByZero IRange
  | SimplifiableValue IRange (Term Value) (Term Value)
  | SimplifiableObservation IRange (Term Observation) (Term Observation)

derive instance genericWarning :: Generic Warning _

instance eqWarning :: Eq Warning where
  eq = genericEq

instance ordWarning :: Ord Warning where
  compare = genericCompare

instance showWarning :: Show Warning where
  show (NegativePayment _) = "The contract can make a non-positive payment"
  show (NegativeDeposit _) = "The contract can make a non-positive deposit"
  show (TimeoutNotIncreasing _) = "Timeouts should always increase in value"
  show (UnreachableCase _) = "This case will never be used"
  show (UnreachableContract _) = "This contract is unreachable"
  show (UndefinedUse _) = "The contract tries to Use a ValueId that has not been defined in a Let"
  show (ShadowedLet _) = "Let is redefining a ValueId that already exists"
  show (DivisionByZero _) = "Scale construct divides by zero"
  show (SimplifiableValue _ oriVal newVal) = "The value \"" <> (show oriVal) <> "\" can be simplified to \"" <> (show newVal) <> "\""
  show (SimplifiableObservation _ oriVal newVal) = "The observation \"" <> (show oriVal) <> "\" can be simplified to \"" <> (show newVal) <> "\""

getWarningRange :: Warning -> IRange
getWarningRange (NegativePayment range) = range

getWarningRange (NegativeDeposit range) = range

getWarningRange (TimeoutNotIncreasing range) = range

getWarningRange (UnreachableCase range) = range

getWarningRange (UnreachableContract range) = range

getWarningRange (UndefinedUse range) = range

getWarningRange (ShadowedLet range) = range

getWarningRange (DivisionByZero range) = range

getWarningRange (SimplifiableValue range _ _) = range

getWarningRange (SimplifiableObservation range _ _) = range

newtype State
  = State
  { holes :: Holes
  , maxTimeout :: MaxTimeout
  , letBindings :: Set ValueId
  , warnings :: Set Warning
  }

derive instance newtypeState :: Newtype State _

derive newtype instance semigroupState :: Semigroup State

derive newtype instance monoidState :: Monoid State

_holes :: Lens' State Holes
_holes = _Newtype <<< prop (SProxy :: SProxy "holes")

_warnings :: Lens' State (Set Warning)
_warnings = _Newtype <<< prop (SProxy :: SProxy "warnings")

termToRange :: forall a. Show a => a -> { row :: Int, column :: Int } -> IRange
termToRange a { row, column } =
  { startLineNumber: row
  , startColumn: column
  , endLineNumber: row
  , endColumn: column + (length (show a))
  }

newtype LintEnv
  = LintEnv
  { letBindings :: Set ValueId
  , maxTimeout :: MaxTimeout
  }

derive instance newtypeLintEnv :: Newtype LintEnv _

derive newtype instance semigroupLintEnv :: Semigroup LintEnv

derive newtype instance monoidLintEnv :: Monoid LintEnv

_letBindings :: Lens' LintEnv (Set ValueId)
_letBindings = _Newtype <<< prop (SProxy :: SProxy "letBindings")

_maxTimeout :: Lens' LintEnv Timeout
_maxTimeout = _Newtype <<< prop (SProxy :: SProxy "maxTimeout") <<< _Newtype

data TemporarySimplification a b
  = ConstantSimp
    Position
    Boolean -- Is simplified (it is not just a constant that was already a constant)
    a -- Constant
  | ValueSimp
    Position
    Boolean -- Is simplified (only root, no subtrees)
    (Term b) -- Value

getSimpPosition :: forall a b. TemporarySimplification a b -> Position
getSimpPosition (ConstantSimp pos _ _) = pos

getSimpPosition (ValueSimp pos _ _) = pos

isSimplified :: forall a b. TemporarySimplification a b -> Boolean
isSimplified (ConstantSimp _ simp _) = simp

isSimplified (ValueSimp _ simp _) = simp

getValue :: forall a b. (a -> Term b) -> TemporarySimplification a b -> Term b
getValue f (ConstantSimp _ _ c) = f c

getValue _ (ValueSimp _ _ v) = v

simplifyTo :: forall a b. TemporarySimplification a b -> Position -> TemporarySimplification a b
simplifyTo (ConstantSimp _ _ c) pos = (ConstantSimp pos true c)

simplifyTo (ValueSimp _ _ c) pos = (ValueSimp pos true c)

markSimplification :: forall a b. Show b => (a -> Term b) -> (IRange -> Term b -> Term b -> Warning) -> Term b -> TemporarySimplification a b -> CMS.State State Unit
markSimplification f c oriVal x
  | isSimplified x = do
    modifying _warnings (Set.insert (c (termToRange oriVal (getPosition oriVal)) oriVal (getValue f x)))
    pure unit
  | otherwise = pure unit

constToObs :: Boolean -> Term Observation
constToObs true = Term TrueObs { row: 0, column: 0 }

constToObs false = Term FalseObs { row: 0, column: 0 }

constToVal :: BigInteger -> Term Value
constToVal x = Term (Constant (Term x { row: 0, column: 0 })) { row: 0, column: 0 }

-- | We lintContract through a contract term collecting all warnings and holes etc so that we can display them in the editor
-- | The aim here is to only traverse the contract once since we are concerned about performance with the linting
-- FIXME: There is a bug where if you create holes with the same name in different When blocks they are missing from
-- the final lint result. After debugging it's strange because they seem to exist in intermediate states.
lint :: Term Contract -> State
lint contract = state
  where
  state = CMS.execState (lintContract mempty contract) mempty

lintContract :: LintEnv -> Term Contract -> CMS.State State Unit
lintContract env (Term Close _) = pure unit

lintContract env (Term t@(Pay acc payee token payment cont) pos) = do
  let
    gatherHoles = getHoles acc <> getHoles payee <> getHoles token
  modifying _holes gatherHoles
  sa <- lintValue env payment
  case sa of
    (ConstantSimp _ _ c)
      | c <= zero -> do
        modifying _warnings (Set.insert (NegativePayment (termToRange t pos)))
        pure unit
    _ -> do
      pure unit
  markSimplification constToVal SimplifiableValue payment sa
  lintContract env cont

lintContract env (Term (If obs c1 c2) _) = do
  sa <- lintObservation env obs
  lintContract env c1
  lintContract env c2
  case sa of
    (ConstantSimp _ _ c) ->
      if c then do
        modifying _warnings (Set.insert (UnreachableContract (termToRange c2 (getPosition c2))))
        pure unit
      else do
        modifying _warnings (Set.insert (UnreachableContract (termToRange c1 (getPosition c1))))
        pure unit
    _ -> do
      markSimplification constToObs SimplifiableObservation obs sa
      pure unit

lintContract env (Term (When cases hole@(Hole _ _ _) cont) _) = do
  traverse_ (lintCase env) cases
  modifying _holes (insertHole hole)
  lintContract env cont
  pure unit

lintContract env (Term (When cases timeoutTerm@(Term timeout pos) cont) _) = do
  let
    timeoutNotIncreasing = if timeout > (view _maxTimeout env) then mempty else Set.singleton (TimeoutNotIncreasing (termToRange timeout pos))

    newEnv = (over _maxTimeout (max timeout)) env
  traverse_ (lintCase newEnv) cases
  modifying _holes (insertHole timeoutTerm)
  modifying _warnings (Set.union timeoutNotIncreasing)
  lintContract newEnv cont
  pure unit

lintContract env (Term (Let valueIdTerm@(Term valueId pos) value cont) _) = do
  let
    shadowedLet = if Set.member valueId (view _letBindings env) then Set.singleton (ShadowedLet (termToRange valueId pos)) else mempty

    newEnv = over _letBindings (Set.insert valueId) env
  modifying _warnings (Set.union shadowedLet)
  sa <- lintValue env value
  markSimplification constToVal SimplifiableValue value sa
  lintContract newEnv cont

lintContract env (Term (Let valueIdTerm@(Hole _ _ _) value cont) _) = do
  let
    gatherHoles = getHoles valueIdTerm
  modifying _holes gatherHoles
  sa <- lintValue env value
  markSimplification constToVal SimplifiableValue value sa
  lintContract env cont

lintContract env hole@(Hole _ _ _) = do
  modifying _holes (insertHole hole)
  pure unit

lintObservation :: LintEnv -> Term Observation -> CMS.State State (TemporarySimplification Boolean Observation)
lintObservation env t@(Term (AndObs a b) pos) = do
  sa <- lintObservation env a
  sb <- lintObservation env b
  case sa /\ sb of
    (ConstantSimp _ _ v /\ _) -> pure (if v then simplifyTo sb pos else ConstantSimp pos true false)
    (_ /\ ConstantSimp _ _ v) -> pure (if v then simplifyTo sa pos else ConstantSimp pos true false)
    _ -> do
      markSimplification constToObs SimplifiableObservation a sa
      markSimplification constToObs SimplifiableObservation b sb
      pure (ValueSimp pos false t)

lintObservation env t@(Term (OrObs a b) pos) = do
  sa <- lintObservation env a
  sb <- lintObservation env b
  case sa /\ sb of
    (ConstantSimp _ _ v /\ _) -> pure (if v then ConstantSimp pos true true else simplifyTo sb pos)
    (_ /\ ConstantSimp _ _ v) -> pure (if v then ConstantSimp pos true true else simplifyTo sa pos)
    _ -> do
      markSimplification constToObs SimplifiableObservation a sa
      markSimplification constToObs SimplifiableObservation b sb
      pure (ValueSimp pos false t)

lintObservation env t@(Term (NotObs a) pos) = do
  sa <- lintObservation env a
  case sa of
    (ConstantSimp _ _ c) -> pure (ConstantSimp pos true (not c))
    _ -> do
      markSimplification constToObs SimplifiableObservation a sa
      pure (ValueSimp pos false t)

lintObservation env t@(Term (ChoseSomething choiceId) pos) = do
  modifying _holes (getHoles choiceId)
  pure (ValueSimp pos false t)

lintObservation env t@(Term (ValueGE a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  case sa /\ sb of
    (ConstantSimp _ _ c1 /\ ConstantSimp _ _ c2) -> pure (ConstantSimp pos true (c1 >= c2))
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

lintObservation env t@(Term (ValueGT a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  case sa /\ sb of
    (ConstantSimp _ _ c1 /\ ConstantSimp _ _ c2) -> pure (ConstantSimp pos true (c1 > c2))
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

lintObservation env t@(Term (ValueLT a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  case sa /\ sb of
    (ConstantSimp _ _ c1 /\ ConstantSimp _ _ c2) -> pure (ConstantSimp pos true (c1 < c2))
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

lintObservation env t@(Term (ValueLE a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  case sa /\ sb of
    (ConstantSimp _ _ c1 /\ ConstantSimp _ _ c2) -> pure (ConstantSimp pos true (c1 <= c2))
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

lintObservation env t@(Term (ValueEQ a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  case sa /\ sb of
    (ConstantSimp _ _ c1 /\ ConstantSimp _ _ c2) -> pure (ConstantSimp pos true (c1 == c2))
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

lintObservation env t@(Term TrueObs pos) = pure (ConstantSimp pos false true)

lintObservation env t@(Term FalseObs pos) = pure (ConstantSimp pos false false)

lintObservation env hole@(Hole _ _ pos) = do
  modifying _holes (insertHole hole)
  pure (ValueSimp pos false hole)

lintValue :: LintEnv -> Term Value -> CMS.State State (TemporarySimplification BigInteger Value)
lintValue env t@(Term (AvailableMoney acc token) pos) = do
  let
    gatherHoles = getHoles acc <> getHoles token
  modifying _holes gatherHoles
  pure (ValueSimp pos false t)

lintValue env (Term (Constant (Term v pos2)) pos) = pure (ConstantSimp pos false v)

lintValue env t@(Term (Constant h@(Hole _ _ _)) pos) = do
  modifying _holes (insertHole h)
  pure (ValueSimp pos false t)

lintValue env t@(Term (NegValue a) pos) = do
  sa <- lintValue env a
  case sa of
    ConstantSimp _ _ c1 -> pure (ConstantSimp pos true (-c1))
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      pure (ValueSimp pos false t)

lintValue env t@(Term (AddValue a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  case sa /\ sb of
    (ConstantSimp _ _ v1 /\ ConstantSimp _ _ v2) -> pure (ConstantSimp pos true (v1 + v2))
    (ConstantSimp _ _ v /\ _)
      | v == zero -> pure (simplifyTo sb pos)
    (_ /\ ConstantSimp _ _ v)
      | v == zero -> pure (simplifyTo sa pos)
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

lintValue env t@(Term (SubValue a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  case sa /\ sb of
    (ConstantSimp _ _ v1 /\ ConstantSimp _ _ v2) -> pure (ConstantSimp pos true (v1 - v2))
    (ConstantSimp _ _ v /\ _)
      | v == zero -> pure (ValueSimp pos true (Term (NegValue b) pos))
    (_ /\ ConstantSimp _ _ v)
      | v == zero -> pure (simplifyTo sa pos)
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

lintValue env t@(Term (Scale (Term r@(Rational a b) pos2) c) pos) = do
  sc <- lintValue env c
  if (b == zero) then do
    modifying _warnings (Set.insert (DivisionByZero (termToRange r pos2)))
    markSimplification constToVal SimplifiableValue c sc
    pure (ValueSimp pos false t)
  else
    let
      gcdv = gcd a b

      na = a `div` gcdv

      nb = b `div` gcdv

      isSimp = (abs gcdv) > one
    in
      case sc of
        (ConstantSimp _ _ v) -> pure (ConstantSimp pos true (evalValue (makeEnvironment zero zero) (emptyState (Slot zero)) (S.Scale (S.Rational a b) (S.Constant v))))
        (ValueSimp _ _ v) -> do
          if isSimp then
            pure unit
          else do
            markSimplification constToVal SimplifiableValue c sc
          pure (ValueSimp pos isSimp (Term (Scale (Term (Rational na nb) pos2) c) pos))

lintValue env t@(Term (Scale h@(Hole _ _ _) c) pos) = do
  sc <- lintValue env c
  case sc of
    (ConstantSimp _ _ v)
      | v == zero -> pure (ConstantSimp pos true zero)
    _ -> do
      markSimplification constToVal SimplifiableValue c sc
      pure (ValueSimp pos false t)

lintValue env t@(Term (ChoiceValue choiceId a) pos) = do
  modifying _holes (getHoles choiceId)
  pure (ValueSimp pos false t)

lintValue env t@(Term SlotIntervalStart pos) = pure (ValueSimp pos false t)

lintValue env t@(Term SlotIntervalEnd pos) = pure (ValueSimp pos false t)

lintValue env t@(Term (UseValue (Term valueId _)) pos) = do
  let
    undefinedLet = if Set.member valueId (view _letBindings env) then mempty else Set.singleton (UndefinedUse (termToRange t pos))
  modifying _warnings (Set.union undefinedLet)
  pure (ValueSimp pos false t)

lintValue env t@(Term (UseValue hole) pos) = do
  modifying _holes (insertHole hole)
  pure (ValueSimp pos false t)

lintValue env hole@(Hole _ _ pos) = do
  modifying _holes (insertHole hole)
  pure (ValueSimp pos false hole)

lintCase :: LintEnv -> Term Case -> CMS.State State Unit
lintCase env t@(Term (Case action contract) pos) = do
  unReachable <- lintAction env action
  if unReachable then do
    modifying _warnings (Set.insert (UnreachableCase (termToRange t pos)))
    pure unit
  else
    pure unit
  lintContract env contract
  pure unit

lintCase env hole@(Hole _ _ _) = do
  modifying _holes (insertHole hole)
  pure unit

lintAction :: LintEnv -> Term Action -> CMS.State State Boolean
lintAction env t@(Term (Deposit acc party token value) pos) = do
  let
    gatherHoles = getHoles acc <> getHoles party <> getHoles token
  modifying _holes (gatherHoles)
  sa <- lintValue env value
  case sa of
    (ConstantSimp _ _ v)
      | v <= zero -> do
        modifying _warnings (Set.insert (NegativeDeposit (termToRange t pos)))
        pure false
    _ -> do
      markSimplification constToVal SimplifiableValue value sa
      pure false

lintAction env (Term (Choice choiceId bounds) _) = do
  modifying _holes (getHoles choiceId <> getHoles bounds)
  pure false

lintAction env (Term (Notify obs) _) = do
  sa <- lintObservation env obs
  case sa of
    (ConstantSimp _ _ c)
      | not c -> pure true
    _ -> do
      markSimplification constToObs SimplifiableObservation obs sa
      pure false

lintAction env hole@(Hole _ _ _) = do
  modifying _holes (insertHole hole)
  pure false

suggestions :: Boolean -> String -> IRange -> Array CompletionItem
suggestions stripParens contract range =
  fromMaybe [] do
    parsedContract <- hush $ parseContract contract
    let
      (Holes holes) = view _holes (lint parsedContract)
    v <- Map.lookup "monaco_suggestions" holes
    { head } <- Array.uncons $ Set.toUnfoldable v
    pure $ holeSuggestions stripParens range head

-- FIXME: We have multiple model markers, 1 per quick fix. This is wrong though, we need only 1 but in MarloweCodeActionProvider we want to run the code
-- to generate the quick fixes from this single model marker
markers :: String -> Array IMarkerData
markers contract = case lint <$> parseContract contract of
  Left EmptyInput -> []
  Left e@(ContractParseError { message, row, column, token }) ->
    let
      whiteSpaceChar c = Set.member c $ Set.fromFoldable $ map codePointFromChar [ '\n', '\r', ' ', '\t' ]

      word = takeWhile (not <<< whiteSpaceChar) token
    in
      [ { startColumn: column
        , startLineNumber: row
        , endColumn: column + (length word)
        , endLineNumber: row
        , message: message
        , severity: markerSeverity "Error"
        , code: ""
        , source: ""
        }
      ]
  Right state ->
    let
      holesMarkers = state ^. (_holes <<< to holesToMarkers)

      warningsMarkers = state ^. (_warnings <<< to Set.toUnfoldable <<< to (map warningToMarker))
    in
      holesMarkers <> warningsMarkers

-- other types of warning could do with being refactored to a Warning ADT first so we don't need to repeat ourselves
holesToMarkers :: Holes -> Array IMarkerData
holesToMarkers (Holes holes) =
  let
    (allHoles :: Array _) = Set.toUnfoldable $ fold $ Map.values holes
  in
    foldMap holeToMarkers allHoles

holeToMarker :: MarloweHole -> Map String (Array Argument) -> String -> IMarkerData
holeToMarker hole@(MarloweHole { name, marloweType, row, column }) m constructorName =
  { startColumn: column
  , startLineNumber: row
  , endColumn: column + (length name) + 1
  , endLineNumber: row
  , message: "Found hole of type " <> (dropEnd 4 $ show marloweType)
  , severity: markerSeverity "Warning"
  , code: ""
  , source: ""
  }
  where
  dropEnd :: Int -> String -> String
  dropEnd n = fromCodePointArray <<< Array.dropEnd n <<< toCodePointArray

holeToMarkers :: MarloweHole -> Array IMarkerData
holeToMarkers hole@(MarloweHole { name, marloweType, row, column }) =
  let
    m = getMarloweConstructors marloweType

    constructors = take 1 $ Set.toUnfoldable $ Map.keys m
  in
    map (holeToMarker hole m) constructors

markerToHole :: IMarkerData -> MarloweType -> MarloweHole
markerToHole { startColumn, startLineNumber } marloweType = MarloweHole { name: "unknown", marloweType, row: startLineNumber, column: startColumn }

warningToMarker :: Warning -> IMarkerData
warningToMarker warning =
  let
    { startColumn, startLineNumber, endColumn, endLineNumber } = getWarningRange warning
  in
    { startColumn
    , startLineNumber
    , endColumn
    , endLineNumber
    , message: show warning
    , severity: markerSeverity "Warning"
    , code: ""
    , source: ""
    }

format :: String -> String
format contractString = case parseContract contractString of
  Left _ -> contractString
  Right contract -> show $ pretty contract

provideCodeActions :: Uri -> Array IMarkerData -> Array CodeAction
provideCodeActions uri markers' =
  (flip foldMap) markers' \(marker@{ message, startLineNumber, startColumn, endLineNumber, endColumn }) -> case regex "Found hole of type (\\w+)" noFlags of
    Left _ -> []
    Right r -> case readMarloweType =<< (join <<< (flip index 1)) =<< match r (message <> "Type") of
      Nothing -> []
      Just BigIntegerType -> []
      Just StringType -> []
      Just marloweType ->
        let
          m = getMarloweConstructors marloweType

          hole = markerToHole marker marloweType

          (constructors :: Array _) = Set.toUnfoldable $ Map.keys m

          range =
            { startLineNumber
            , startColumn
            , endLineNumber
            , endColumn
            }

          actions =
            mapFlipped constructors \constructorName ->
              let
                text = constructMarloweType constructorName hole m

                edit = { resource: uri, edit: { range, text } }
              in
                { title: constructorName, edit: { edits: [ edit ] }, kind: "quickfix" }
        in
          actions
