module Editor.View
  ( editorPreferencesSelect
  , compileButton
  , simulateButton
  , editorPane
  , editorFeedback
  ) where

import Editor.Types
import AjaxUtils (ajaxErrorPane)
import Bootstrap (btn, card, cardHeader, cardHeader_, cardBody_, customSelect, empty, listGroupItem_, listGroup_, nbsp)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Lens (_Right, preview, to, view)
import Data.Maybe (Maybe(Just), fromMaybe)
import Data.String as String
import Editor.State (initEditor)
import Effect.Aff.Class (class MonadAff)
import Halogen.HTML (ClassName(ClassName), ComponentHTML, HTML, a, button, code_, div, div_, option, p_, pre, pre_, select, slot, text)
import Halogen.HTML.Events (onClick, onDragOver, onDrop, onSelectedIndexChange)
import Halogen.HTML.Properties (class_, classes, disabled, id_, selected, value)
import Halogen.Monaco (KeyBindings(..), monacoComponent)
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (CompilationError(CompilationError, RawError), InterpreterError(CompilationErrors, TimeoutError), Warning, _InterpreterResult, _Warning)
import Language.Haskell.Monaco as HM
import LocalStorage (Key)
import Network.RemoteData (RemoteData(..), _Success, isLoading)
import Prelude (const, map, pure, show, unit, ($), (<$>), (<<<), (<>), (==))
import Types (ChildSlots, _editorSlot, HAction(..), View(..))

-- renders the editor preferences select dropdown
editorPreferencesSelect :: forall p. KeyBindings -> HTML p Action
editorPreferencesSelect active =
  select
    [ class_ customSelect
    , onSelectedIndexChange
        ( \index ->
            SetKeyBindings <$> Array.index allKeyBindings index
        )
    ]
    (editor <$> allKeyBindings)
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

-- renders the compile button
compileButton :: forall p a. CompilationState a -> HTML p HAction
compileButton state =
  button
    [ classes [ btn, ClassName "btn-green" ]
    , onClick $ const $ Just CompileProgram
    , disabled (isLoading state)
    ]
    [ btnText ]
  where
  btnText = case state of
    Loading -> icon Spinner
    _ -> text "Compile"

-- renders the simulator button
simulateButton :: forall p a. CompilationState a -> HTML p HAction
simulateButton state =
  button
    [ classes [ btn, ClassName "btn-turquoise" ]
    , onClick $ const $ Just (ChangeView Simulations)
    , disabled isDisabled
    ]
    [ text "Simulate" ]
  where
  isDisabled = case state of
    Success (Right _) -> false
    _ -> true

-- renders the editor pane
editorPane ::
  forall m.
  MonadAff m =>
  Maybe String ->
  Key ->
  State ->
  ComponentHTML Action ChildSlots m
editorPane initialContents bufferLocalStorageKey state@(State { keyBindings }) =
  div
    [ class_ (ClassName "code-editor")
    , onDragOver $ Just <<< HandleDragEvent
    , onDrop $ Just <<< HandleDropEvent
    ]
    [ slot
        _editorSlot
        unit
        (monacoComponent (HM.settings (initEditor initialContents bufferLocalStorageKey state)))
        unit
        (Just <<< HandleEditorMessage)
    , case keyBindings of
        Vim -> pre [ id_ "statusline" ] [ nbsp ]
        _ -> pre [ id_ "statusline", class_ $ ClassName "hidden" ] [ nbsp ]
    ]

-- renders the editor feedback div (showing compilation errors and/or warnings)
editorFeedback ::
  forall m a.
  MonadAff m =>
  State ->
  CompilationState a ->
  ComponentHTML Action ChildSlots m
editorFeedback editorState@(State { feedbackPaneMinimised }) compilationState =
  div
    [ class_ $ ClassName "editor-feedback-container" ]
    [ div
        [ classes feedbackPaneClasses ]
        [ div
            [ class_ $ ClassName "editor-feedback-header" ]
            [ p_ [ summaryText ]
            , case compilationState of
                Success (Left error) -> minMaxButton
                Failure error -> minMaxButton
                _ -> empty
            ]
        , div
            [ class_ $ ClassName "editor-feedback-body" ]
            [ errorList
            , warningList
            ]
        ]
    ]
  where
  feedbackPaneClasses =
    if feedbackPaneMinimised then
      [ ClassName "editor-feedback", ClassName "minimised" ]
    else
      [ ClassName "editor-feedback" ]

  summaryText = case compilationState of
    NotAsked -> text "Not compiled"
    Loading -> text "Compiling ..."
    Success (Left error) -> text "Compilation failed"
    Failure error -> text "Compilation failed"
    _ -> text "Compilation successful"

  minMaxButton =
    a
      [ class_ btn
      , onClick $ const $ Just ToggleFeedbackPane
      ]
      if feedbackPaneMinimised then
        [ icon ArrowUp ]
      else
        [ icon ArrowDown ]

  errorList = case compilationState of
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
          compilationState

-- renders all interpreter errors
interpreterErrorPane :: forall p. InterpreterError -> Array (HTML p Action)
interpreterErrorPane (TimeoutError error) = [ listGroupItem_ [ div_ [ text error ] ] ]

interpreterErrorPane (CompilationErrors errors) = map compilationErrorPane errors

-- renders a compilation error
compilationErrorPane :: forall p. CompilationError -> HTML p Action
compilationErrorPane (RawError error) =
  div
    [ classes [ card, ClassName "raw-error" ] ]
    [ cardHeader_ [ text "Compilation Error" ]
    , cardBody_ [ text error ]
    ]

compilationErrorPane (CompilationError error) =
  div
    [ classes [ card, ClassName "compilation-error" ] ]
    [ div
        [ class_ cardHeader ]
        [ text $ "Compilation Error, Line " <> show error.row <> ", Column " <> show error.column
        , nbsp
        , a
            [ onClick $ const $ Just $ ScrollTo { lineNumber: error.row, column: error.column } ]
            [ text "(jump)" ]
        ]
    , cardBody_
        [ code_ [ pre_ [ text $ String.joinWith "\n" error.text ] ] ]
    ]

-- renders all compilation warnings
compilationWarningsPane :: forall p. Array Warning -> HTML p Action
compilationWarningsPane warnings = listGroup_ (listGroupItem_ <<< pure <<< compilationWarningPane <$> warnings)

-- renders a compilation warning
compilationWarningPane :: forall p. Warning -> HTML p Action
compilationWarningPane warning = div [ class_ $ ClassName "compilation-warning" ] [ text $ view _Warning warning ]
