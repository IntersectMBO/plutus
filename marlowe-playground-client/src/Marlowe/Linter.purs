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
import Control.MonadZero (guard)
import Data.Array (catMaybes, fold, foldMap, take, (:))
import Data.Array as Array
import Data.Array.NonEmpty (index)
import Data.BigInteger (BigInteger)
import Data.Either (Either(..), hush)
import Data.Functor (mapFlipped)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Eq (genericEq)
import Data.Generic.Rep.Ord (genericCompare)
import Data.Lens (Lens', over, to, view, (^.))
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.String (codePointFromChar, fromCodePointArray, length, takeWhile, toCodePointArray)
import Data.String.Regex (match, regex)
import Data.String.Regex.Flags (noFlags)
import Data.Symbol (SProxy(..))
import Data.Tuple.Nested (type (/\), (/\))
import Marlowe.Holes (Action(..), Argument, Case(..), Contract(..), Holes(..), MarloweHole(..), MarloweType(..), Observation(..), Term(..), Value(..), ValueId, constructMarloweType, getHoles, getMarloweConstructors, holeSuggestions, insertHole, readMarloweType)
import Marlowe.Parser (ContractParseError(..), parseContract)
import Marlowe.Semantics (Timeout)
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
  | UninitializedUse IRange
  | ShadowedLet IRange
  | TrueObservation IRange
  | FalseObservation IRange

derive instance genericWarning :: Generic Warning _

instance eqWarning :: Eq Warning where
  eq = genericEq

instance ordWarning :: Ord Warning where
  compare = genericCompare

instance showWarning :: Show Warning where
  show (NegativePayment _) = "The contract can make a negative payment"
  show (NegativeDeposit _) = "The contract can make a negative deposit"
  show (TimeoutNotIncreasing _) = "Timeouts should always increase in value"
  show (UninitializedUse _) = "The contract tries to Use a ValueId that has not been defined in a Let"
  show (ShadowedLet _) = "Let is redefining a ValueId that already exists"
  show (TrueObservation _) = "This Observation will always evaluate to True"
  show (FalseObservation _) = "This Observation will always evaluate to False"

getWarningRange :: Warning -> IRange
getWarningRange (NegativePayment range) = range

getWarningRange (NegativeDeposit range) = range

getWarningRange (TimeoutNotIncreasing range) = range

getWarningRange (UninitializedUse range) = range

getWarningRange (ShadowedLet range) = range

getWarningRange (TrueObservation range) = range

getWarningRange (FalseObservation range) = range

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

_maxTimeout :: Lens' State Timeout
_maxTimeout = _Newtype <<< prop (SProxy :: SProxy "maxTimeout") <<< _Newtype

_warnings :: Lens' State (Set Warning)
_warnings = _Newtype <<< prop (SProxy :: SProxy "warnings")

_letBindings :: Lens' State (Set ValueId)
_letBindings = _Newtype <<< prop (SProxy :: SProxy "letBindings")

termToRange :: forall a. Show a => a -> { row :: Int, column :: Int } -> IRange
termToRange a { row, column } =
  { startLineNumber: row
  , startColumn: column
  , endLineNumber: row
  , endColumn: column + (length (show a))
  }

-- | We go through a contract term collecting all warnings and holes etc so that we can display them in the editor
-- | The aim here is to only traverse the contract once since we are concerned about performance with the linting
-- FIXME: There is a bug where if you create holes with the same name in different When blocks they are missing from
-- the final lint result. After debugging it's strange because they seem to exist in intermediate states.
lint :: Term Contract -> State
lint = go mempty
  where
  go :: State -> Term Contract -> State
  go state (Term Close _) = state

  go state (Term (Pay acc payee token payment contract) _) =
    let
      gatherHoles = getHoles acc <> getHoles payee <> getHoles token

      newState =
        state
          # over _holes gatherHoles
          # over _warnings (maybeInsert (NegativePayment <$> negativeValue payment))
    in
      go newState contract <> lintValue newState payment

  go state (Term (If obs c1 c2) _) = go state c1 <> go state c2 <> lintObservation state obs

  go state (Term (When cases timeoutTerm contract) _) =
    let
      (states /\ contracts) = collectFromTuples (map (lintCase state) cases)

      newState = case timeoutTerm of
        (Term timeout pos) ->
          let
            insertTimeoutNotIncreasing = if timeout > (view _maxTimeout state) then identity else Set.insert (TimeoutNotIncreasing (termToRange timeout pos))
          in
            (fold states)
              # over _holes (insertHole timeoutTerm)
              # over _maxTimeout (max timeout)
              # over _warnings insertTimeoutNotIncreasing
        _ ->
          (fold states)
            # over _holes (insertHole timeoutTerm)
    in
      foldMap (go newState) (contract : catMaybes contracts)

  go state (Term (Let valueIdTerm value contract) _) =
    let
      gatherHoles = getHoles valueIdTerm

      newState = case valueIdTerm of
        (Term valueId pos) ->
          let
            shadowedLet = if Set.member valueId (view _letBindings state) then Set.singleton (ShadowedLet (termToRange valueId pos)) else mempty
          in
            state
              # over _holes gatherHoles
              # over _warnings (maybeInsert (NegativePayment <$> negativeValue value))
              # over _letBindings (Set.insert valueId)
              # over _warnings (Set.union shadowedLet)
        _ ->
          state
            # over _holes gatherHoles
            # over _warnings (maybeInsert (NegativePayment <$> negativeValue value))
    in
      go newState contract <> lintValue newState value

  go state hole@(Hole _ _ _) = over _holes (insertHole hole) state

lintObservation :: State -> Term Observation -> State
lintObservation state (Term (AndObs a b) _) = lintObservation state a <> lintObservation state b

lintObservation state (Term (OrObs a b) _) = lintObservation state a <> lintObservation state b

lintObservation state (Term (NotObs a) _) = lintObservation state a

lintObservation state (Term (ChoseSomething choiceId) _) = over _holes (getHoles choiceId) state

lintObservation state (Term (ValueGE a b) _) = lintValue state a <> lintValue state b

lintObservation state (Term (ValueGT a b) _) = lintValue state a <> lintValue state b

lintObservation state (Term (ValueLT a b) _) = lintValue state a <> lintValue state b

lintObservation state (Term (ValueLE a b) _) = lintValue state a <> lintValue state b

lintObservation state (Term (ValueEQ a b) _) = lintValue state a <> lintValue state b

lintObservation state (Term TrueObs pos) = over _warnings (Set.insert (TrueObservation (termToRange TrueObs pos))) state

lintObservation state (Term FalseObs pos) = over _warnings (Set.insert (FalseObservation (termToRange FalseObs pos))) state

lintObservation state hole@(Hole _ _ _) = over _holes (insertHole hole) state

lintValue :: State -> Term Value -> State
lintValue state (Term (AvailableMoney acc token) _) =
  let
    gatherHoles = getHoles acc <> getHoles token
  in
    over _holes (gatherHoles) state

lintValue state (Term (Constant a) _) = over _holes (insertHole a) state

lintValue state (Term (NegValue a) _) = lintValue state a

lintValue state (Term (AddValue a b) _) = lintValue state a <> lintValue state b

lintValue state (Term (SubValue a b) _) = lintValue state a <> lintValue state b

lintValue state (Term (Scale a b) _) = lintValue state b

lintValue state (Term (ChoiceValue choiceId a) _) =
  let
    newState = over _holes (getHoles choiceId) state
  in
    lintValue newState a

lintValue state (Term SlotIntervalStart _) = state

lintValue state (Term SlotIntervalEnd _) = state

lintValue state (Term (UseValue (Term valueId pos)) _) =
  let
    addWarnings = if Set.member valueId (view _letBindings state) then identity else Set.insert (UninitializedUse (termToRange valueId pos))
  in
    state
      # over _holes (getHoles valueId)
      # over _warnings addWarnings

lintValue state (Term (UseValue hole) _) = over _holes (insertHole hole) state

lintValue state hole@(Hole _ _ _) = over _holes (insertHole hole) state

maybeInsert :: forall a. Ord a => Maybe a -> Set a -> Set a
maybeInsert Nothing xs = xs

maybeInsert (Just x) xs = Set.insert x xs

collectFromTuples :: forall a b. Array (a /\ b) -> Array a /\ Array b
collectFromTuples = foldMap (\(a /\ b) -> [ a ] /\ [ b ])

lintCase :: State -> Term Case -> State /\ Maybe (Term Contract)
lintCase state (Term (Case action contract) _) =
  let
    newState =
      state
        # over _warnings (maybeInsert (negativeDeposit action))
  in
    lintAction newState action /\ Just contract

lintCase state hole@(Hole _ _ _) = over _holes (insertHole hole) state /\ Nothing

lintAction :: State -> Term Action -> State
lintAction state (Term (Deposit acc party token value) _) =
  let
    gatherHoles = getHoles acc <> getHoles party <> getHoles token

    newState = over _holes (gatherHoles) state
  in
    lintValue newState value

lintAction state (Term (Choice choiceId bounds) _) = over _holes (getHoles choiceId <> getHoles bounds) state

lintAction state (Term (Notify obs) _) = lintObservation state obs

lintAction state hole@(Hole _ _ _) = over _holes (insertHole hole) state

negativeDeposit :: Term Action -> Maybe Warning
negativeDeposit (Term (Deposit _ _ _ value) _) = NegativeDeposit <$> negativeValue value

negativeDeposit _ = Nothing

negativeValue :: Term Value -> Maybe IRange
negativeValue term@(Term _ pos) = do
  v <- constantValue term
  guard (v < zero)
  pure (termToRange v pos)

negativeValue _ = Nothing

constantValue :: Term Value -> Maybe BigInteger
constantValue (Term (Constant (Term v _)) _) = Just v

constantValue (Term (NegValue v) _) = negate <$> constantValue v

constantValue (Term (AddValue a b) _) = do
  va <- constantValue a
  vb <- constantValue b
  pure (va + vb)

constantValue (Term (SubValue a b) _) = do
  va <- constantValue a
  vb <- constantValue b
  pure (va - vb)

constantValue _ = Nothing

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
  , severity: markerSeverity "Hint"
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
