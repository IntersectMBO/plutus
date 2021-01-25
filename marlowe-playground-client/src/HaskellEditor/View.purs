module HaskellEditor.View where

import Prelude hiding (div)
import BottomPanel.Types (Action(..)) as BottomPanel
import BottomPanel.View (render) as BottomPanel
import Data.Array as Array
import Data.Either (Either(..))
import Data.Enum (toEnum, upFromIncluding)
import Data.Lens (has, to, view, (^.))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), split)
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Examples.Haskell.Contracts as HE
import Halogen (ClassName(..), ComponentHTML, liftEffect)
import Halogen.Classes (aHorizontal, analysisPanel, closeDrawerArrowIcon, codeEditor, collapsed, footerPanelBg, group, minimizeIcon)
import Halogen.Classes as Classes
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (HTML, a, button, code_, div, div_, img, option, pre_, section, select, slot, text)
import Halogen.HTML.Events (onClick, onSelectedIndexChange)
import Halogen.HTML.Properties (alt, class_, classes, disabled, src)
import Halogen.HTML.Properties as HTML
import Halogen.Monaco (monacoComponent)
import HaskellEditor.Types (Action(..), BottomPanelView(..), State, _bottomPanelState, _compilationResult, _haskellEditorKeybindings)
import Language.Haskell.Interpreter (CompilationError(..), InterpreterError(..), InterpreterResult(..))
import Language.Haskell.Monaco as HM
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _haskellEditorSlot)
import Monaco (getModel, setValue) as Monaco
import Network.RemoteData (RemoteData(..), _Loading, isLoading, isSuccess)
import StaticData as StaticData

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div_
    [ section [ class_ (ClassName "code-panel") ]
        [ div [ classes [ codeEditor ] ]
            [ haskellEditor state ]
        ]
    , renderSubmodule _bottomPanelState BottomPanelAction (BottomPanel.render panelTitles wrapBottomPanelContents) state
    ]
  where
  panelTitles =
    [ { title: "Generated code", view: GeneratedOutputView, classes: [] }
    , { title: "Errors", view: ErrorsView, classes: [] }
    ]

  wrapBottomPanelContents panelView = BottomPanel.PanelAction <$> panelContents state panelView

otherActions :: forall p. State -> HTML p Action
otherActions state =
  div [ classes [ group ] ]
    [ editorOptions state
    , compileButton state
    , sendResultButton state "Send To Simulator" SendResultToSimulator
    -- FIXME: I think we want to change this action to be called from the simulator
    --        with the action "soon to be implemented" ViewAsBlockly
    -- , sendResultButton state "Send To Blockly" SendResultToBlockly
    ]

editorOptions :: forall p. State -> HTML p Action
editorOptions state =
  div [ class_ (ClassName "editor-options") ]
    [ select
        [ HTML.id_ "editor-options"
        , class_ (ClassName "dropdown-header")
        , HTML.value $ show $ state ^. _haskellEditorKeybindings
        , onSelectedIndexChange (\idx -> ChangeKeyBindings <$> toEnum idx)
        ]
        (map keybindingItem (upFromIncluding bottom))
    ]
  where
  keybindingItem item =
    if state ^. _haskellEditorKeybindings == item then
      option [ class_ (ClassName "selected-item"), HTML.value (show item) ] [ text $ show item ]
    else
      option [ HTML.value (show item) ] [ text $ show item ]

haskellEditor ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
haskellEditor state = slot _haskellEditorSlot unit component unit (Just <<< HandleEditorMessage)
  where
  setup editor =
    liftEffect do
      -- TODO we shouldn't access local storage from the view
      mContents <- LocalStorage.getItem StaticData.bufferLocalStorageKey
      let
        contents = fromMaybe HE.escrow mContents
      model <- Monaco.getModel editor
      Monaco.setValue model contents

  component = monacoComponent $ HM.settings setup

compileButton :: forall p. State -> HTML p Action
compileButton state =
  button [ onClick $ const $ Just Compile ]
    [ text (if has (_compilationResult <<< _Loading) state then "Compiling..." else "Compile") ]

sendResultButton :: forall p. State -> String -> Action -> HTML p Action
sendResultButton state msg action =
  let
    compilationResult = view _compilationResult state
  in
    case view _compilationResult state of
      Success (Right (InterpreterResult result)) ->
        button
          [ onClick $ const $ Just action
          , disabled (isLoading compilationResult || (not isSuccess) compilationResult)
          ]
          [ text msg ]
      _ -> text ""

panelContents :: forall p. State -> BottomPanelView -> HTML p Action
panelContents state GeneratedOutputView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents ]
    ] case view _compilationResult state of
    Success (Right (InterpreterResult result)) ->
      [ div [ classes [ ClassName "code-editor", ClassName "expanded", ClassName "code" ] ]
          numberedText
      ]
      where
      numberedText = (code_ <<< Array.singleton <<< text) <$> split (Pattern "\n") result.result
    _ -> [ text "There is no generated code" ]

panelContents state ErrorsView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents ]
    ] case view _compilationResult state of
    Success (Left (TimeoutError error)) -> [ text error ]
    Success (Left (CompilationErrors errors)) -> map compilationErrorPane errors
    _ -> [ text "No errors" ]

compilationErrorPane :: forall p. CompilationError -> HTML p Action
compilationErrorPane (RawError error) = div_ [ text error ]

compilationErrorPane (CompilationError error) =
  div
    [ class_ $ ClassName "compilation-error"
    ]
    [ text $ "Line " <> show error.row <> ", Column " <> show error.column <> ":"
    , code_ [ pre_ [ text $ String.joinWith "\n" error.text ] ]
    ]
