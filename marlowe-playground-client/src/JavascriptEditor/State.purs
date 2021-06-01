module JavascriptEditor.State
  ( handleAction
  , mkEditor
  , editorGetValue
  ) where

import Prelude hiding (div)
import BottomPanel.State (handleAction) as BottomPanel
import BottomPanel.Types (Action(..), State) as BottomPanel
import CloseAnalysis (analyseClose)
import Control.Monad.Reader (class MonadAsk)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Lens (assign, modifying, over, set, use, view)
import Data.List ((:))
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (unwrap)
import Data.String (drop, joinWith, length, take)
import Data.Tuple.Nested ((/\))
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import Env (Env)
import Examples.JS.Contracts as JSE
import Halogen (Component, HalogenM, gets, liftEffect, modify_, query)
import Halogen.Extra (mapSubmodule)
import Halogen.HTML (HTML)
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import Halogen.Monaco (Message, Query, monacoComponent)
import JavascriptEditor.Types (Action(..), BottomPanelView(..), CompilationState(..), State, _bottomPanelState, _compilationResult, _decorationIds, _keybindings, _metadataHintInfo)
import Language.Javascript.Interpreter (InterpreterResult(..))
import Language.Javascript.Interpreter as JSI
import Language.Javascript.Monaco as JSM
import MainFrame.Types (ChildSlots, _jsEditorSlot)
import Marlowe.Extended (Contract)
import Marlowe.Extended.Metadata (MetadataHintInfo, getMetadataHintInfo)
import Marlowe.Template (getPlaceholderIds, typeToLens, updateTemplateContent)
import Monaco (IRange, getModel, isError, setValue)
import Network.RemoteData (RemoteData(..))
import SessionStorage as SessionStorage
import StaticAnalysis.Reachability (analyseReachability)
import StaticAnalysis.StaticTools (analyseContract)
import StaticAnalysis.Types (AnalysisExecutionState(..), MultiStageAnalysisData(..), _analysisExecutionState, _analysisState, _templateContent)
import StaticData (jsBufferLocalStorageKey)
import StaticData as StaticData
import Text.Parsing.StringParser.Basic (lines)

toBottomPanel ::
  forall m a.
  Functor m =>
  HalogenM (BottomPanel.State BottomPanelView) (BottomPanel.Action BottomPanelView Action) ChildSlots Void m a ->
  HalogenM State Action ChildSlots Void m a
toBottomPanel = mapSubmodule _bottomPanelState BottomPanelAction

checkDecorationPosition :: Int -> Maybe IRange -> Maybe IRange -> Boolean
checkDecorationPosition numLines (Just { endLineNumber }) (Just { startLineNumber }) = (endLineNumber == decorationHeaderLines) && (startLineNumber == numLines - decorationFooterLines + 1)

checkDecorationPosition _ _ _ = false

handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction (HandleEditorMessage (Monaco.TextChanged text)) =
  ( do
      -- TODO: This handler manages the logic of having a restricted range that cannot be modified. But the
      --       current implementation uses editorSetValue to overwrite the editor contents with the last
      --       correct value (taken from session storage). By using editorSetValue inside the TextChanged handler
      --       the events get fired multiple times on init, which makes hasUnsavedChanges always true for a new
      --       JS project or a project load.
      --
      --       Once the PR 2498 gets merged, I want to try changing the web-commons Monaco component so that the
      --       TextChanged handler returns an IModelContentChangedEvent instead of a string. That event cointains
      --       information of the range of the modifications, and if the action was triggered by an undo/redo
      --       action. With that information we can reimplement this by firing an undo event if a "read only"
      --       decoration. At this moment I'm not sure if that will solve the bubble problem but at least it will
      --       allow us to decouple from session storage.
      let
        prunedText = pruneJSboilerplate text

        numLines = Array.length $ lines text
      mDecorIds <- gets $ view _decorationIds
      case mDecorIds of
        Just decorIds -> do
          mRangeHeader <- query _jsEditorSlot unit (Monaco.GetDecorationRange decorIds.topDecorationId identity)
          mRangeFooter <- query _jsEditorSlot unit (Monaco.GetDecorationRange decorIds.bottomDecorationId identity)
          mContent <- liftEffect $ SessionStorage.getItem jsBufferLocalStorageKey
          if ((mContent == Nothing) || (mContent == Just prunedText)) then
            -- The case where `mContent == Just prunedText` is to prevent potential infinite loops, it should not happen
            assign _compilationResult NotCompiled
          else
            if checkJSboilerplate text && checkDecorationPosition numLines mRangeHeader mRangeFooter then
              ( do
                  liftEffect $ SessionStorage.setItem jsBufferLocalStorageKey prunedText
                  assign _compilationResult NotCompiled
              )
            else
              editorSetValue (fromMaybe "" mContent)
        Nothing -> editorSetValue prunedText
  )

handleAction (ChangeKeyBindings bindings) = do
  assign _keybindings bindings
  void $ query _jsEditorSlot unit (Monaco.SetKeyBindings bindings unit)

handleAction Compile = do
  maybeModel <- query _jsEditorSlot unit (Monaco.GetModel identity)
  compilationResult <- case maybeModel of
    Nothing -> pure NotCompiled
    Just model -> do
      assign _compilationResult Compiling
      maybeMarkers <- query _jsEditorSlot unit (Monaco.GetModelMarkers identity)
      case map ((List.filter (\e -> isError e.severity)) <<< Array.toUnfoldable) maybeMarkers of
        Just ({ message, startLineNumber, startColumn } : _) ->
          pure $ CompilationError
            $ JSI.CompilationError
                { row: startLineNumber
                , column: startColumn
                , text: [ message ]
                }
        _ -> do
          res <- liftAff $ JSI.eval model
          case res of
            Left err -> pure $ CompilationError err
            Right result -> do
              let
                contract :: Contract
                contract = (unwrap result).result

                metadataHints :: MetadataHintInfo
                metadataHints = getMetadataHintInfo contract
              modify_
                $ over (_analysisState <<< _templateContent) (updateTemplateContent $ getPlaceholderIds contract)
                <<< set _metadataHintInfo metadataHints
              pure $ CompiledSuccessfully result
  assign _compilationResult compilationResult
  case compilationResult of
    (CompilationError _) -> handleAction $ BottomPanelAction (BottomPanel.ChangePanel ErrorsView)
    _ -> pure unit

handleAction (BottomPanelAction (BottomPanel.PanelAction action)) = handleAction action

handleAction (BottomPanelAction action) = do
  toBottomPanel (BottomPanel.handleAction action)

handleAction SendResultToSimulator = pure unit

handleAction (InitJavascriptProject metadataHints prunedContent) = do
  editorSetValue prunedContent
  assign _metadataHintInfo metadataHints
  liftEffect $ SessionStorage.setItem jsBufferLocalStorageKey prunedContent

handleAction (SetIntegerTemplateParam templateType key value) = modifying (_analysisState <<< _templateContent <<< typeToLens templateType) (Map.insert key value)

handleAction (MetadataAction _) = pure unit

handleAction AnalyseContract = analyze (WarningAnalysis Loading) $ analyseContract

handleAction AnalyseReachabilityContract =
  analyze (ReachabilityAnalysis AnalysisNotStarted)
    $ analyseReachability

handleAction AnalyseContractForCloseRefund =
  analyze (CloseAnalysis AnalysisNotStarted)
    $ analyseClose

handleAction ClearAnalysisResults = assign (_analysisState <<< _analysisExecutionState) NoneAsked

-- This function runs a static analysis to the compiled code if it compiled successfully.
analyze ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  AnalysisExecutionState ->
  (Contract -> HalogenM State Action ChildSlots Void m Unit) ->
  HalogenM State Action ChildSlots Void m Unit
analyze initialAnalysisState doAnalyze = do
  compilationResult <- use _compilationResult
  case compilationResult of
    CompiledSuccessfully (InterpreterResult interpretedResult) -> doAnalyze interpretedResult.result
    _ -> pure unit

decorationHeader :: String
decorationHeader =
  """import {
    PK, Role, Account, Party, ada, AvailableMoney, Constant, ConstantParam,
    NegValue, AddValue, SubValue, MulValue, Scale, ChoiceValue, SlotIntervalStart,
    SlotIntervalEnd, UseValue, Cond, AndObs, OrObs, NotObs, ChoseSomething,
    ValueGE, ValueGT, ValueLT, ValueLE, ValueEQ, TrueObs, FalseObs, Deposit,
    Choice, Notify, Close, Pay, If, When, Let, Assert, SomeNumber, AccountId,
    ChoiceId, Token, ValueId, Value, EValue, Observation, Bound, Action, Payee,
    Case, Timeout, ETimeout, SlotParam, Contract
} from 'marlowe-js';

(function (): Contract {"""

decorationFooter :: String
decorationFooter = "})"

decorationHeaderLines :: Int
decorationHeaderLines = Array.length $ lines decorationHeader

decorationFooterLines :: Int
decorationFooterLines = Array.length $ lines decorationFooter

lengthOfHeader :: Int
lengthOfHeader = length decorationHeader

lengthOfFooter :: Int
lengthOfFooter = length decorationFooter

editorSetValue ::
  forall m.
  MonadAff m =>
  String ->
  HalogenM State Action ChildSlots Void m Unit
editorSetValue contents = do
  let
    decoratedContent = joinWith "\n" [ decorationHeader, contents, decorationFooter ]

    numLines = Array.length $ lines decoratedContent

    decorationOptions = { isWholeLine: true, className: "monaco-readonly-decoration", linesDecorationsClassName: "" }

    topRange = { startLineNumber: 1, startColumn: 0, endLineNumber: decorationHeaderLines, endColumn: 0 }

    bottomRange = { startLineNumber: (numLines - decorationFooterLines + 1), startColumn: 0, endLineNumber: numLines, endColumn: 0 }
  void $ query _jsEditorSlot unit $ Monaco.SetText decoratedContent unit
  -- TODO: Refactor HandleEditorMessage Monaco.TextChanged so we can store the array of decorations instead of having to split them between top
  --       and bottom
  mDecorationIds <- use _decorationIds
  let
    oldHeaderDecoration = maybe [] (Array.singleton <<< _.topDecorationId) mDecorationIds

    oldFooterDecoration = maybe [] (Array.singleton <<< _.bottomDecorationId) mDecorationIds
  mNewHeaderIds <-
    query _jsEditorSlot unit
      $ Monaco.SetDeltaDecorations oldHeaderDecoration [ { range: topRange, options: decorationOptions } ] identity
  mNewFooterIds <-
    query _jsEditorSlot unit
      $ Monaco.SetDeltaDecorations oldFooterDecoration [ { range: bottomRange, options: decorationOptions } ] identity
  case mNewHeaderIds /\ mNewFooterIds of
    Just [ topDecorationId ] /\ Just [ bottomDecorationId ] -> assign _decorationIds $ Just { topDecorationId, bottomDecorationId }
    _ -> pure unit

checkJSboilerplate :: String -> Boolean
checkJSboilerplate content =
  let
    header = (take (lengthOfHeader + 1) content)

    footer = (drop (length content - lengthOfFooter - 1) content)
  in
    (header == decorationHeader <> "\n") && (footer == "\n" <> decorationFooter)

pruneJSboilerplate :: String -> String
pruneJSboilerplate content =
  let
    noHeader = (drop (lengthOfHeader + 1) content)
  in
    take (length noHeader - lengthOfFooter - 1) noHeader

editorGetValue ::
  forall m.
  MonadAff m =>
  HalogenM State Action ChildSlots Void m (Maybe String)
editorGetValue = do
  mContent <- query _jsEditorSlot unit (Monaco.GetText identity)
  pure
    ( map
        pruneJSboilerplate
        mContent
    )

mkEditor :: forall m. MonadEffect m => MonadAff m => Component HTML Query Unit Message m
mkEditor = monacoComponent $ JSM.settings setup
  where
  setup editor =
    liftEffect do
      mContents <- SessionStorage.getItem StaticData.jsBufferLocalStorageKey
      let
        contents = fromMaybe JSE.example mContents

        decoratedContent = joinWith "\n" [ decorationHeader, contents, decorationFooter ]

        numLines = Array.length $ lines decoratedContent
      model <- getModel editor
      setValue model decoratedContent
      pure unit
