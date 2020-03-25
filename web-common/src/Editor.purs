module Editor
  ( Action(..)
  , PreferencesAction(..)
  , Preferences(..)
  , KeyBindings(..)
  , initEditor
  , handleAction
  , readKeyBindings
  , loadPreferences
  , allKeyBindings
  , editorView
  , editorFeedback
  , compileButton
  , setPreferences
  , saveBuffer
  , withEditor
  ) where

import Ace.Config as Ace.Config
import Ace.EditSession as Session
import Ace.Editor as AceEditor
import Ace.Editor as Editor
import Ace.Halogen.Component (AceMessage(..), AceQuery(..), Autocomplete(Live), aceComponent)
import Ace.Types (Editor)
import AjaxUtils (ajaxErrorPane)
import Bootstrap (btn, btnDanger, btnPrimary, btnSecondary, btnSuccess, customSelect, empty, formGroup, listGroupItem_, listGroup_, pullRight)
import Control.Alternative ((<|>))
import Control.Monad.Trans.Class (lift)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Lens', _Right, preview, to, view)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe, maybe)
import Data.String as String
import Data.Symbol (class IsSymbol, SProxy(..))
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import FileEvents (preventDefault, readFileFromDragEvent)
import Halogen (HalogenM, Slot, liftEffect, query, request)
import Halogen.HTML (ClassName(ClassName), ComponentHTML, HTML, button, code_, div, div_, h3_, option, pre_, select, slot, small, text)
import Halogen.HTML.Events (onClick, onDragOver, onDrop, onSelectedIndexChange)
import Halogen.HTML.Properties (class_, classes, disabled, id_, selected, value)
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (CompilationError(CompilationError, RawError), InterpreterError(CompilationErrors, TimeoutError), InterpreterResult, Warning, _InterpreterResult, _Warning)
import LocalStorage (Key(..))
import LocalStorage as LocalStorage
import Network.RemoteData (RemoteData(..), _Success, isLoading)
import Prelude (class Eq, class Ord, class Show, Unit, bind, const, discard, join, map, pure, show, unit, void, ($), (<$>), (<<<), (<>), (==))
import Prim.Row as Row
import Servant.PureScript.Ajax (AjaxError)
import Web.HTML.Event.DragEvent (DragEvent)

data Action
  = HandleEditorMessage AceMessage
  | HandleDragEvent DragEvent
  | HandleDropEvent DragEvent
  | ScrollTo { row :: Int, column :: Int }
  | SetPreferences PreferencesAction

handleAction :: forall m. MonadAff m => Key -> Action -> Editor -> m Unit
handleAction bufferLocalStorageKey (HandleEditorMessage (TextChanged text)) _ = saveBuffer bufferLocalStorageKey text

handleAction _ (SetPreferences preferencesAction) editor = setPreferences preferencesAction editor

handleAction _ (HandleDragEvent event) _ = liftEffect $ preventDefault event

handleAction _ (ScrollTo { row, column }) editor =
  liftEffect do
    AceEditor.gotoLine row (Just column) (Just true) editor
    AceEditor.focus editor

handleAction bufferLocalStorageKey (HandleDropEvent event) editor =
  liftAff do
    liftEffect $ preventDefault event
    contents <- readFileFromDragEvent event
    liftEffect $ void $ AceEditor.setValue contents (Just 1) editor
    saveBuffer bufferLocalStorageKey contents

data PreferencesAction
  = SetKeyBindings KeyBindings

------------------------------------------------------------
data KeyBindings
  = Ace
  | Vim
  | Emacs

derive instance eqKeyBindings :: Eq KeyBindings

derive instance genericKeyBindings :: Generic KeyBindings _

instance showKeyBindings :: Show KeyBindings where
  show = genericShow

allKeyBindings :: Array KeyBindings
allKeyBindings = [ Ace, Emacs, Vim ]

readKeyBindings :: String -> KeyBindings
readKeyBindings "Emacs" = Emacs

readKeyBindings "Vim" = Vim

readKeyBindings _ = Ace

aceBindingName :: KeyBindings -> String
aceBindingName Ace = ""

aceBindingName Vim = "ace/keyboard/vim"

aceBindingName Emacs = "ace/keyboard/emacs"

------------------------------------------------------------
data Preferences
  = Preferences { keyBindings :: KeyBindings }

derive instance eqPreferences :: Eq Preferences

derive instance genericPreferences :: Generic Preferences _

instance showPreferences :: Show Preferences where
  show = genericShow

------------------------------------------------------------
keybindingsLocalStorageKey :: Key
keybindingsLocalStorageKey = Key "EditorPreferences.KeyBindings"

setPreferences :: forall m. MonadEffect m => PreferencesAction -> Editor -> m Unit
setPreferences (SetKeyBindings binding) editor =
  liftEffect do
    Editor.setKeyboardHandler (aceBindingName binding) editor
    LocalStorage.setItem keybindingsLocalStorageKey (show binding)

loadPreferences :: forall m. MonadEffect m => m Preferences
loadPreferences =
  liftEffect do
    keyBindings <- maybe Ace readKeyBindings <$> LocalStorage.getItem keybindingsLocalStorageKey
    pure $ Preferences { keyBindings }

saveBuffer :: forall m. MonadEffect m => Key -> String -> m Unit
saveBuffer bufferLocalStorageKey text = liftEffect $ LocalStorage.setItem bufferLocalStorageKey text

initEditor ∷
  forall m.
  MonadAff m =>
  Maybe String -> LocalStorage.Key -> Preferences -> Editor -> m Unit
initEditor initialContents bufferLocalStorageKey preferences@(Preferences { keyBindings }) editor =
  liftEffect
    $ do
        void $ Ace.Config.set Ace.Config.basePath "ace"
        savedContents <- liftEffect $ LocalStorage.getItem bufferLocalStorageKey
        let
          contents = fromMaybe "" (savedContents <|> initialContents)
        void $ Editor.setValue contents (Just 1) editor
        --
        setPreferences (SetKeyBindings keyBindings) editor
        --
        Editor.setTheme "ace/theme/monokai" editor
        Editor.setShowPrintMargin false editor
        --
        session <- Editor.getSession editor
        Session.setMode "ace/mode/haskell" session

type CompilationState a
  = RemoteData AjaxError (Either InterpreterError (InterpreterResult a))

_warnings :: forall s a. Lens' { warnings :: a | s } a
_warnings = prop (SProxy :: SProxy "warnings")

editorView ::
  forall m label _1 slots.
  Row.Cons label (Slot AceQuery AceMessage Unit) _1 slots =>
  IsSymbol label =>
  MonadAff m =>
  Maybe String ->
  SProxy label ->
  LocalStorage.Key ->
  Preferences ->
  ComponentHTML Action slots m
editorView initialContents slotLabel bufferLocalStorageKey preferences@(Preferences { keyBindings }) =
  div
    [ id_ "editor"
    , class_ (ClassName "code-editor")
    , onDragOver $ Just <<< HandleDragEvent
    , onDrop $ Just <<< HandleDropEvent
    ]
    [ slot
        slotLabel
        unit
        (aceComponent (initEditor initialContents bufferLocalStorageKey preferences) (Just Live))
        unit
        (Just <<< HandleEditorMessage)
    , editorPreferencesPane keyBindings
    ]

editorFeedback ::
  forall m slots a.
  MonadAff m =>
  CompilationState a ->
  ComponentHTML Action slots m
editorFeedback state =
  div_
    [ errorList
    , warningList
    ]
  where
  errorList = case state of
    Success (Left error) -> listGroup_ (interpreterErrorPane error)
    Failure error -> ajaxErrorPane error
    _ -> empty

  warningList =
    fromMaybe empty
      $ preview
          ( _Success
              <<< _Right
              <<< _InterpreterResult
              <<< _warnings
              <<< to compilationWarningsPane
          )
          state

editorPreferencesPane :: forall p. KeyBindings -> HTML p Action
editorPreferencesPane active =
  div
    [ id_ "editor-preferences"
    , class_ formGroup
    ]
    [ select
        [ class_ customSelect
        , onSelectedIndexChange
            ( \index ->
                SetPreferences <<< SetKeyBindings <$> Array.index allKeyBindings index
            )
        ]
        (editor <$> allKeyBindings)
    ]
  where
  editor keyBindings =
    option
      [ value $ show keyBindings
      , selected (active == keyBindings)
      ]
      [ text $ editorName keyBindings ]

  editorName Ace = "Default"

  editorName Emacs = "Emacs"

  editorName Vim = "Vim"

compileButton :: forall p action a. action -> CompilationState a -> HTML p action
compileButton action state =
  button
    [ id_ "compile"
    , classes [ btn, btnClass ]
    , onClick $ const $ Just action
    , disabled (isLoading state)
    ]
    [ btnText ]
  where
  btnClass = case state of
    Success (Right _) -> btnSuccess
    Success (Left _) -> btnDanger
    Failure _ -> btnDanger
    Loading -> btnSecondary
    NotAsked -> btnPrimary

  btnText = case state of
    Loading -> icon Spinner
    _ -> text "Compile"

interpreterErrorPane :: forall p. InterpreterError -> Array (HTML p Action)
interpreterErrorPane (TimeoutError error) = [ listGroupItem_ [ div_ [ text error ] ] ]

interpreterErrorPane (CompilationErrors errors) = map compilationErrorPane errors

compilationErrorPane :: forall p. CompilationError -> HTML p Action
compilationErrorPane (RawError error) = div_ [ text error ]

compilationErrorPane (CompilationError error) =
  div
    [ class_ $ ClassName "compilation-error"
    , onClick $ const $ Just $ ScrollTo { row: error.row, column: error.column }
    ]
    [ small [ class_ pullRight ] [ text "jump" ]
    , h3_ [ text $ "Line " <> show error.row <> ", Column " <> show error.column <> ":" ]
    , code_ [ pre_ [ text $ String.joinWith "\n" error.text ] ]
    ]

compilationWarningsPane :: forall p. Array Warning -> HTML p Action
compilationWarningsPane warnings = listGroup_ (listGroupItem_ <<< pure <<< compilationWarningPane <$> warnings)

compilationWarningPane :: forall p. Warning -> HTML p Action
compilationWarningPane warning = div [ class_ $ ClassName "compilation-warning" ] [ text $ view _Warning warning ]

-- | Handles the messy business of running an editor command if and
-- only if the editor is up and running.
withEditor ::
  forall label slotIndex _1 state action slots output m a.
  Row.Cons label (Slot AceQuery AceMessage slotIndex) _1 slots =>
  Ord slotIndex =>
  MonadEffect m =>
  IsSymbol label =>
  SProxy label ->
  slotIndex ->
  (Editor -> m a) ->
  HalogenM state action slots output m (Maybe a)
withEditor label slotIndex action = do
  mEditor <- query label slotIndex $ request GetEditor
  case join mEditor of
    Just editor -> lift $ Just <$> action editor
    _ -> pure Nothing
