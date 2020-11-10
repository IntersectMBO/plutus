module JavascriptEditor.State where

import Prelude hiding (div)
import Control.Monad.Maybe.Extra (hoistMaybe)
import Control.Monad.Maybe.Trans (runMaybeT)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Lens (assign, to, use, view)
import Data.List ((:))
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (drop, joinWith, length, take)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import Examples.JS.Contracts as JSE
import Halogen (Component, HalogenM, gets, liftEffect, query)
import Halogen.Blockly as Blockly
import Halogen.HTML (HTML)
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import Halogen.Monaco (Message, Query, monacoComponent)
import JavascriptEditor.Types (Action(..), CompilationState(..), State, _compilationResult, _decorationIds, _keybindings, _showBottomPanel)
import Language.Javascript.Interpreter (_result)
import Language.Javascript.Interpreter as JSI
import Language.Javascript.Monaco as JSM
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _blocklySlot, _jsEditorSlot)
import Marlowe (SPParams_)
import Monaco (IRange, getModel, isError, setValue)
import Servant.PureScript.Settings (SPSettings_)
import StaticData (jsBufferLocalStorageKey)
import StaticData as StaticData
import Text.Parsing.StringParser.Basic (lines)

checkDecorationPosition :: Int -> Maybe IRange -> Maybe IRange -> Boolean
checkDecorationPosition numLines (Just { endLineNumber }) (Just { startLineNumber }) = (endLineNumber == decorationHeaderLines) && (startLineNumber == numLines - decorationFooterLines + 1)

checkDecorationPosition _ _ _ = false

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction _ (HandleEditorMessage (Monaco.TextChanged text)) =
  ( do
      let
        prunedText = pruneJSboilerplate text

        numLines = Array.length $ lines text
      mDecorIds <- gets $ view _decorationIds
      case mDecorIds of
        Just decorIds -> do
          mRangeHeader <- query _jsEditorSlot unit (Monaco.GetDecorationRange decorIds.topDecorationId identity)
          mRangeFooter <- query _jsEditorSlot unit (Monaco.GetDecorationRange decorIds.bottomDecorationId identity)
          mContent <- liftEffect $ LocalStorage.getItem jsBufferLocalStorageKey
          if checkJSboilerplate text && checkDecorationPosition numLines mRangeHeader mRangeFooter then
            ( do
                liftEffect $ LocalStorage.setItem jsBufferLocalStorageKey prunedText
                assign _compilationResult NotCompiled
            )
          else
            if (mContent == Just prunedText) then
              -- To prevent infinite loops (should not be needed)
              assign _compilationResult NotCompiled
            else
              editorSetValue (fromMaybe "" mContent)
        Nothing -> editorSetValue prunedText
  )

handleAction _ (ChangeKeyBindings bindings) = do
  assign _keybindings bindings
  void $ query _jsEditorSlot unit (Monaco.SetKeyBindings bindings unit)

handleAction settings Compile = do
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
            Right result -> pure $ CompiledSuccessfully result
  assign _compilationResult compilationResult
  assign _showBottomPanel true
  editorResize

handleAction _ (LoadScript key) = do
  case Map.lookup key StaticData.demoFilesJS of
    Nothing -> pure unit
    Just contents -> do
      editorSetValue contents

handleAction _ (ShowBottomPanel val) = do
  assign _showBottomPanel val
  editorResize

handleAction _ SendResultToSimulator = pure unit

handleAction _ SendResultToBlockly = do
  mContract <- use _compilationResult
  case mContract of
    CompiledSuccessfully result -> do
      let
        source = view (_result <<< to show) result
      void $ query _blocklySlot unit (Blockly.SetCode source unit)
    _ -> pure unit

editorResize :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorResize = void $ query _jsEditorSlot unit (Monaco.Resize unit)

decorationHeader :: String
decorationHeader =
  """import {
    PK, Role, Account, Party, ada, AvailableMoney, Constant, NegValue, AddValue,
    SubValue, MulValue, Scale, ChoiceValue, SlotIntervalStart, SlotIntervalEnd,
    UseValue, Cond, AndObs, OrObs, NotObs, ChoseSomething, ValueGE, ValueGT,
    ValueLT, ValueLE, ValueEQ, TrueObs, FalseObs, Deposit, Choice, Notify,
    Close, Pay, If, When, Let, Assert, SomeNumber, AccountId, ChoiceId, Token,
    ValueId, Value, EValue, Observation, Bound, Action, Payee, Case, Contract
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
  void $ query _jsEditorSlot unit $ Monaco.SetText decoratedContent unit
  mTopDecorationId <- query _jsEditorSlot unit $ Monaco.SetDeltaDecorations 1 decorationHeaderLines identity
  mBottomDecorationId <- query _jsEditorSlot unit $ Monaco.SetDeltaDecorations (numLines - decorationFooterLines + 1) numLines identity
  void
    $ runMaybeT do
        topDecorationId <- hoistMaybe mTopDecorationId
        bottomDecorationId <- hoistMaybe mBottomDecorationId
        assign _decorationIds $ Just { topDecorationId, bottomDecorationId }

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
      mContents <- LocalStorage.getItem StaticData.jsBufferLocalStorageKey
      let
        contents = fromMaybe JSE.escrow mContents

        decoratedContent = joinWith "\n" [ decorationHeader, contents, decorationFooter ]

        numLines = Array.length $ lines decoratedContent
      model <- getModel editor
      setValue model decoratedContent
      pure unit
