module Editor.State
  ( initialState
  , handleAction
  , saveBuffer
  , initEditor
  ) where

import Control.Alternative ((<|>))
import Data.Foldable (for_)
import Data.Lens (assign, modifying, use)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Ord (clamp)
import Editor.Lenses (_currentCodeIsCompiled, _feedbackPaneDragStart, _feedbackPaneExtend, _feedbackPaneMinimised, _feedbackPanePreviousExtend, _keyBindings, _lastCompiledCode)
import Editor.Types (State(State), Action(..), readKeyBindings)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import Halogen (HalogenM, liftEffect, query, tell)
import Halogen.Monaco (KeyBindings(..))
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import Language.Haskell.Interpreter (SourceCode(SourceCode))
import LocalStorage (Key, getItem, setItem)
import MainFrame.Lenses (_editorSlot)
import MainFrame.Types (ChildSlots)
import Monaco (Editor, getModel, layout, focus, setPosition, setValue) as Monaco
import Prelude (Unit, bind, discard, not, pure, show, unit, void, (+), (-), ($), (<$>), (==))
import StaticData (keybindingsLocalStorageKey)
import Web.Event.Extra (preventDefault, readFileFromDragEvent)
import Web.UIEvent.MouseEvent (pageY)

initialState :: forall m. MonadEffect m => m State
initialState =
  liftEffect do
    keyBindings <- loadKeyBindings
    pure
      $ State
          { keyBindings
          , feedbackPaneMinimised: true
          , lastCompiledCode: Nothing
          , currentCodeIsCompiled: false
          , feedbackPaneDragStart: Nothing
          , feedbackPaneExtend: 0
          , feedbackPanePreviousExtend: 0
          }

handleAction ::
  forall action output m.
  MonadEffect m =>
  MonadAff m =>
  Key ->
  Action ->
  HalogenM State action ChildSlots output m Unit
handleAction bufferLocalStorageKey Init = do
  binding <- loadKeyBindings
  assign _keyBindings binding
  handleAction bufferLocalStorageKey (SetKeyBindings binding)

handleAction _ (HandleEditorMessage Monaco.EditorReady) = pure unit

handleAction bufferLocalStorageKey (HandleEditorMessage (Monaco.TextChanged text)) = do
  lastCompiledCode <- use _lastCompiledCode
  case lastCompiledCode of
    Just (SourceCode code) -> assign _currentCodeIsCompiled (code == text)
    Nothing -> assign _currentCodeIsCompiled false
  liftEffect $ saveBuffer bufferLocalStorageKey text

handleAction _ (SetKeyBindings binding) = do
  void $ query _editorSlot unit $ tell $ Monaco.SetKeyBindings binding
  void $ query _editorSlot unit $ tell $ Monaco.Focus
  void $ query _editorSlot unit $ tell $ Monaco.Resize
  assign _keyBindings binding
  liftEffect $ setItem keybindingsLocalStorageKey (show binding)

handleAction _ ToggleFeedbackPane = modifying _feedbackPaneMinimised not

handleAction _ (HandleDragEvent event) = liftEffect $ preventDefault event

handleAction _ (ScrollTo position) = do
  void $ query _editorSlot unit $ tell $ Monaco.SetPosition position
  void $ query _editorSlot unit $ tell $ Monaco.Focus

handleAction bufferLocalStorageKey (HandleDropEvent event) = do
  liftEffect $ preventDefault event
  contents <- liftAff $ readFileFromDragEvent event
  void $ query _editorSlot unit $ tell $ Monaco.SetText contents
  void $ query _editorSlot unit $ tell $ Monaco.SetPosition { column: 1, lineNumber: 1 }
  saveBuffer bufferLocalStorageKey contents

handleAction _ (SetFeedbackPaneDragStart event) = do
  liftEffect $ preventDefault event
  assign _feedbackPaneDragStart $ Just $ pageY event

handleAction _ ClearFeedbackPaneDragStart = do
  feedbackPaneExtend <- use _feedbackPaneExtend
  assign _feedbackPaneDragStart Nothing
  assign _feedbackPanePreviousExtend feedbackPaneExtend

handleAction _ (FixFeedbackPaneExtend mouseY) = do
  feedbackPaneDragStart <- use _feedbackPaneDragStart
  feedbackPanePreviousExtend <- use _feedbackPanePreviousExtend
  for_ feedbackPaneDragStart
    $ \startMouseY ->
        assign _feedbackPaneExtend
          $ clamp 0 100
          $ startMouseY
          - mouseY
          + feedbackPanePreviousExtend

------------------------------------------------------------
loadKeyBindings :: forall m. MonadEffect m => m KeyBindings
loadKeyBindings = maybe DefaultBindings readKeyBindings <$> liftEffect (getItem keybindingsLocalStorageKey)

saveBuffer :: forall m. MonadEffect m => Key -> String -> m Unit
saveBuffer bufferLocalStorageKey text = liftEffect $ setItem bufferLocalStorageKey text

initEditor ::
  forall m.
  MonadEffect m =>
  Maybe String ->
  Key ->
  State ->
  Monaco.Editor ->
  m Unit
initEditor initialContents bufferLocalStorageKey state@(State { keyBindings }) editor =
  liftEffect do
    savedContents <- getItem bufferLocalStorageKey
    let
      contents = fromMaybe "" (savedContents <|> initialContents)
    model <- Monaco.getModel editor
    Monaco.setValue model contents
    Monaco.layout editor
    Monaco.setPosition editor { lineNumber: 1, column: 1 }
    Monaco.focus editor
