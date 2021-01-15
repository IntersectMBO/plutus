module Editor.State where

import Editor.Types
import Control.Alternative ((<|>))
import Data.Lens (assign, modifying, use)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import Halogen (HalogenM, liftEffect, query, tell)
import Halogen.Monaco (KeyBindings(..))
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import Language.Haskell.Interpreter (SourceCode(SourceCode))
import LocalStorage (Key)
import LocalStorage as LocalStorage
import Monaco (Editor, getModel, layout, focus, setPosition, setValue) as Monaco
import Prelude (Unit, bind, discard, not, pure, show, unit, void, ($), (<$>), (==))
import Types (ChildSlots, _editorSlot)
import Web.Event.Extra (preventDefault, readFileFromDragEvent)

initialState :: forall m. MonadEffect m => m State
initialState =
  liftEffect do
    keyBindings <- loadKeyBindings
    pure
      $ State
          { keyBindings
          , feedbackPaneMinimised: false
          , lastCompiledCode: Nothing
          , currentCodeIsCompiled: false
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
  liftEffect $ LocalStorage.setItem keybindingsLocalStorageKey (show binding)

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

------------------------------------------------------------
loadKeyBindings :: forall m. MonadEffect m => m KeyBindings
loadKeyBindings = maybe DefaultBindings readKeyBindings <$> liftEffect (LocalStorage.getItem keybindingsLocalStorageKey)

saveBuffer :: forall m. MonadEffect m => Key -> String -> m Unit
saveBuffer bufferLocalStorageKey text = liftEffect $ LocalStorage.setItem bufferLocalStorageKey text

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
    savedContents <- LocalStorage.getItem bufferLocalStorageKey
    let
      contents = fromMaybe "" (savedContents <|> initialContents)
    model <- Monaco.getModel editor
    Monaco.setValue model contents
    Monaco.layout editor
    Monaco.setPosition editor { lineNumber: 1, column: 1 }
    Monaco.focus editor
