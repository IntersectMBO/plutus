module HaskellEditor.View where

import Prelude hiding (div)
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
import Halogen.HTML (HTML, a, button, code_, div, div_, img, option, pre_, section, select, slot, text)
import Halogen.HTML.Events (onClick, onSelectedIndexChange)
import Halogen.HTML.Properties (alt, class_, classes, disabled, src)
import Halogen.HTML.Properties as HTML
import Halogen.Monaco (monacoComponent)
import HaskellEditor.Types (Action(..), State, _compilationResult, _haskellEditorKeybindings, _showBottomPanel)
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
        [ div [ classes (codeEditor $ state ^. _showBottomPanel) ]
            [ haskellEditor state ]
        ]
    , bottomPanel state
    ]

otherActions :: forall p. State -> HTML p Action
otherActions state =
  div [ classes [ group ] ]
    [ editorOptions state
    , compileButton state
    , sendResultButton state "Send To Simulator" SendResultToSimulator
    , sendResultButton state "Send To Blockly" SendResultToBlockly
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

bottomPanel :: forall p. State -> HTML p Action
bottomPanel state =
  div
    ( [ classes
          ( if showingBottomPanel then
              [ analysisPanel ]
            else
              [ analysisPanel, collapsed ]
          )
      ]
    )
    [ div
        [ classes [ footerPanelBg, ClassName "flip-x" ] ]
        [ section [ classes [ ClassName "panel-header", aHorizontal ] ]
            [ div [ classes [ ClassName "panel-sub-header-main", aHorizontal ] ]
                [ div [ class_ (ClassName "minimize-icon-container") ]
                    [ a [ onClick $ const $ Just $ ShowBottomPanel (state ^. _showBottomPanel <<< to not) ]
                        [ img [ classes (minimizeIcon $ state ^. _showBottomPanel), src closeDrawerArrowIcon, alt "close drawer icon" ] ]
                    ]
                ]
            ]
        , section
            [ classes [ ClassName "panel-sub-header", aHorizontal, ClassName "panel-contents" ]
            ]
            (resultPane state)
        ]
    ]
  where
  showingBottomPanel = state ^. _showBottomPanel

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

resultPane :: forall p. State -> Array (HTML p Action)
resultPane state = case state ^. _showBottomPanel, view _compilationResult state of
  true, Success (Right (InterpreterResult result)) ->
    [ div [ classes [ ClassName "code-editor", ClassName "expanded", ClassName "code" ] ]
        numberedText
    ]
    where
    numberedText = (code_ <<< Array.singleton <<< text) <$> split (Pattern "\n") result.result
  true, Success (Left (TimeoutError error)) -> [ text error ]
  true, Success (Left (CompilationErrors errors)) -> map compilationErrorPane errors
  _, _ -> [ text "" ]

compilationErrorPane :: forall p. CompilationError -> HTML p Action
compilationErrorPane (RawError error) = div_ [ text error ]

compilationErrorPane (CompilationError error) =
  div
    [ class_ $ ClassName "compilation-error"
    ]
    [ text $ "Line " <> show error.row <> ", Column " <> show error.column <> ":"
    , code_ [ pre_ [ text $ String.joinWith "\n" error.text ] ]
    ]
