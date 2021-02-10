module Marlowe.LinterText
  ( AdditionalContext
  , suggestions
  , markers
  , provideCodeActions
  , format
  , marloweHoleToSuggestionText
  ) where

import Prelude
import Data.Array (catMaybes, fold, foldMap, take)
import Data.Array as Array
import Data.Array.NonEmpty (index)
import Data.Either (Either(..), hush)
import Data.Functor (mapFlipped)
import Data.Lens (to, view, (^.))
import Data.List (List(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..), codePointFromChar, contains, fromCodePointArray, length, takeWhile, toCodePointArray)
import Data.String.Regex (match, regex)
import Data.String.Regex.Flags (noFlags)
import Data.Tuple (Tuple(..))
import Effect.Exception.Unsafe (unsafeThrow)
import Help (holeText)
import Marlowe.Holes (Contract, Holes(..), Location(..), MarloweHole(..), MarloweType, Term, TermGenerator, constructMarloweType, getMarloweConstructors, readMarloweType)
import Marlowe.Linter (Warning(..), WarningDetail(..), _holes, _warnings, lint)
import Marlowe.Parser (ContractParseError(..), parseContract)
import Monaco (CodeAction, CompletionItem, IMarkerData, IRange, Uri, completionItemKind, markerSeverity)
import Monaco as Monaco
import StaticAnalysis.Types (ContractPath)
import Text.Extra as Text
import Text.Pretty (pretty)

-- We cannot guarantee at the type level that the only type of location we handle in the Parser is a Range
-- location, so we throw a useful error if we ever get to this situation
locationToRange :: Location -> IRange
locationToRange (Range range) = range

locationToRange (BlockId _) = unsafeThrow "Unexpected BlockId location found in LinterText"

locationToRange NoLocation = unsafeThrow "Unexpected NoLocation found in LinterText"

getWarningRange :: Warning -> IRange
getWarningRange (Warning { location }) = locationToRange location

-- FIXME: We have multiple model markers, 1 per quick fix. This is wrong though, we need only 1 but in MarloweCodeActionProvider we want to run the code
-- to generate the quick fixes from this single model marker
markers :: List ContractPath -> Either ContractParseError (Term Contract) -> Tuple (Array IMarkerData) AdditionalContext
markers unreachablePaths parsedContract = do
  case (lint unreachablePaths <$> parsedContract) of
    Left EmptyInput -> (Tuple [] { warnings: mempty, contract: Nothing })
    Left e@(ContractParseError { message, row, column, token }) ->
      let
        whiteSpaceChar c = Set.member c $ Set.fromFoldable $ map codePointFromChar [ '\n', '\r', ' ', '\t' ]

        word = takeWhile (not <<< whiteSpaceChar) token

        markerData =
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
      in
        (Tuple markerData { warnings: mempty, contract: Nothing })
    Right state ->
      let
        holesMarkers = state ^. (_holes <<< to holesToMarkers)

        warningsMarkers = state ^. (_warnings <<< to Set.toUnfoldable <<< to (map warningToMarker))

        -- we store the current warnings and the parsed contract in the halogen state so that they can be reused
        additionalContext = { warnings: state ^. _warnings, contract: hush parsedContract }
      in
        (Tuple (holesMarkers <> warningsMarkers) additionalContext)

-- other types of warning could do with being refactored to a Warning ADT first so we don't need to repeat ourselves
holesToMarkers :: Holes -> Array IMarkerData
holesToMarkers (Holes holes) =
  let
    (allHoles :: Array _) = Set.toUnfoldable $ fold $ Map.values holes
  in
    foldMap holeToMarkers allHoles

holeToMarker :: MarloweHole -> Map String TermGenerator -> String -> IMarkerData
holeToMarker hole@(MarloweHole { name, marloweType, location }) m constructorName =
  let
    -- If holeToMarker is called with the wrong Location type it will yield incorrect results.
    -- That is why we want to make the Warnings polymorphic to the Location and to separate the linter
    -- in 3. General linter that does not care about Location, MarloweLinter that deals with `Warning IRange`
    -- and BlocklyLinter that deals with `Warning BlocklyId`
    { startColumn, startLineNumber, endColumn, endLineNumber } = locationToRange location

    dropEnd :: Int -> String -> String
    dropEnd n = fromCodePointArray <<< Array.dropEnd n <<< toCodePointArray
  in
    { startColumn
    , startLineNumber
    , endColumn
    , endLineNumber
    , message: holeText marloweType
    , severity: markerSeverity "Warning"
    , code: ""
    , source: "Hole: " <> (dropEnd 4 $ show marloweType)
    }

holeToMarkers :: MarloweHole -> Array IMarkerData
holeToMarkers hole@(MarloweHole { name, marloweType }) =
  let
    m = getMarloweConstructors marloweType

    constructors = take 1 $ Set.toUnfoldable $ Map.keys m
  in
    map (holeToMarker hole m) constructors

markerToHole :: IMarkerData -> MarloweType -> MarloweHole
markerToHole markerData marloweType = MarloweHole { name: "unknown", marloweType, location: Range (Monaco.getRange markerData) }

warningType :: Warning -> String
warningType (Warning { warning }) = case warning of
  NegativePayment -> "NegativePayment"
  NegativeDeposit -> "NegativeDeposit"
  TimeoutNotIncreasing -> "TimeoutNotIncreasing"
  UnreachableCaseEmptyChoice -> "UnreachableCaseEmptyChoice"
  InvalidBound -> "InvalidBound"
  UnreachableCaseFalseNotify -> "UnreachableCaseFalseNotify"
  UnreachableContract -> "UnreachableContract"
  UndefinedChoice -> "UndefinedChoice"
  UndefinedUse -> "UndefinedUse"
  ShadowedLet -> "ShadowedLet"
  DivisionByZero -> "DivisionByZero"
  (SimplifiableValue _ _) -> "SimplifiableValue"
  (SimplifiableObservation _ _) -> "SimplifiableObservation"
  (PayBeforeDeposit _) -> "PayBeforeDeposit"
  (PartialPayment _ _ _ _) -> "PartialPayment"

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
    , source: warningType warning
    }

shortWarning :: WarningDetail -> String
shortWarning (SimplifiableValue _ _) = "Simplify Value"

shortWarning _ = ""

provideLintCodeActions :: Uri -> AdditionalContext -> Array CodeAction
provideLintCodeActions uri { warnings } = catMaybes <<< map codeAction <<< Set.toUnfoldable $ warnings
  where
  codeAction :: Warning -> Maybe CodeAction
  codeAction (Warning { warning, refactoring: Just refactoring }) =
    Just
      { title: shortWarning warning
      , edit: { edits: [ { resource: uri, edit: refactoring } ] }
      , kind: "quickfix"
      }

  codeAction _ = Nothing

provideCodeActions :: Uri -> Array IMarkerData -> AdditionalContext -> Array CodeAction
provideCodeActions uri markers' additionalContext =
  provideLintCodeActions uri additionalContext
    <> (flip foldMap) markers' \(marker@{ source, startLineNumber, startColumn, endLineNumber, endColumn }) -> case regex "Hole: (\\w+)" noFlags of
        Left _ -> []
        Right r -> case readMarloweType =<< (join <<< (flip index 1)) =<< match r (source <> "Type") of
          Nothing -> []
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

type AdditionalContext
  = { warnings :: Set Warning
    , contract :: Maybe (Term Contract)
    }

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

suggestions :: String -> Boolean -> String -> IRange -> AdditionalContext -> Array CompletionItem
suggestions original stripParens contractString range { contract } =
  fromMaybe [] do
    -- there will be no contract if it had errors, this is no good because we want to try to fix this
    -- with contractString, which is a contract that comes from the MarloweCompletionItemProvider with
    -- holes where possible errors are, so it might be able to be parsed.
    parsedContract <- case contract of
      Nothing -> hush $ parseContract contractString
      c -> c
    let
      (Holes holes) = view _holes ((lint Nil) parsedContract)
    v <- Map.lookup "monaco_suggestions" holes
    { head } <- Array.uncons $ Set.toUnfoldable v
    pure $ holeSuggestions original stripParens range head

format :: String -> String
format contractString = case parseContract contractString of
  Left _ -> contractString
  Right contract -> show $ pretty contract
