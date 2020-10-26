module Editor.View where

import Editor.Types
import AjaxUtils (ajaxErrorPane)
import Bootstrap (btn, btnDanger, btnPrimary, btnSecondary, btnSuccess, customSelect, empty, formGroup, listGroupItem_, listGroup_, pullRight)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Lens (_Right, preview, to, view)
import Data.Maybe (Maybe(Just), fromMaybe)
import Data.String as String
import Editor.State (initEditor)
import Effect.Aff.Class (class MonadAff)
import Halogen.HTML (ClassName(ClassName), ComponentHTML, HTML, button, code_, div, div_, h3_, option, pre_, select, slot, small, text)
import Halogen.HTML.Events (onClick, onDragOver, onDrop, onSelectedIndexChange)
import Halogen.HTML.Properties (class_, classes, disabled, id_, selected, value)
import Halogen.Monaco (KeyBindings(..), monacoComponent)
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (CompilationError(CompilationError, RawError), InterpreterError(CompilationErrors, TimeoutError), Warning, _InterpreterResult, _Warning)
import Language.Haskell.Monaco as HM
import LocalStorage (Key)
import Network.RemoteData (RemoteData(..), _Success, isLoading)
import Prelude (const, map, pure, show, unit, ($), (<$>), (<<<), (<>), (==))
import Types (ChildSlots, _editorSlot)

editorView ::
  forall m.
  MonadAff m =>
  Maybe String ->
  Key ->
  State ->
  ComponentHTML Action ChildSlots m
editorView initialContents bufferLocalStorageKey state@(State { keyBindings }) =
  div
    [ id_ "editor"
    , class_ (ClassName "code-editor")
    , onDragOver $ Just <<< HandleDragEvent
    , onDrop $ Just <<< HandleDropEvent
    ]
    [ slot
        _editorSlot
        unit
        (monacoComponent (HM.settings (initEditor initialContents bufferLocalStorageKey state)))
        unit
        (Just <<< HandleEditorMessage)
    , editorPreferencesPane keyBindings
    ]

editorFeedback ::
  forall m a.
  MonadAff m =>
  CompilationState a ->
  ComponentHTML Action ChildSlots m
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
                SetKeyBindings <$> Array.index allKeyBindings index
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

  editorName DefaultBindings = "Default"

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
    , onClick $ const $ Just $ ScrollTo { lineNumber: error.row, column: error.column }
    ]
    [ small [ class_ pullRight ] [ text "jump" ]
    , h3_ [ text $ "Line " <> show error.row <> ", Column " <> show error.column <> ":" ]
    , code_ [ pre_ [ text $ String.joinWith "\n" error.text ] ]
    ]

compilationWarningsPane :: forall p. Array Warning -> HTML p Action
compilationWarningsPane warnings = listGroup_ (listGroupItem_ <<< pure <<< compilationWarningPane <$> warnings)

compilationWarningPane :: forall p. Warning -> HTML p Action
compilationWarningPane warning = div [ class_ $ ClassName "compilation-warning" ] [ text $ view _Warning warning ]
