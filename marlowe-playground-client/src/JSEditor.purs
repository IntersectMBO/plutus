module JSEditor where

import Data.Array as Array
import Data.Enum (toEnum, upFromIncluding)
import Data.Lens (to, view, (^.))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), split)
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Examples.JS.Contracts as JSE
import Halogen (ClassName(..), ComponentHTML, liftEffect)
import Halogen.Classes (aHorizontal, analysisPanel, closeDrawerArrowIcon, codeEditor, collapsed, footerPanelBg, minimizeIcon)
import Halogen.HTML (HTML, a, button, code_, div, div_, img, option, pre_, section, select, slot, text)
import Halogen.HTML.Events (onClick, onSelectedIndexChange)
import Halogen.HTML.Properties (alt, class_, classes, href, src)
import Halogen.HTML.Properties as HTML
import Halogen.Monaco (monacoComponent)
import Language.Javascript.Interpreter (CompilationError(..), InterpreterResult(..))
import Language.Javascript.Monaco as JSM
import LocalStorage as LocalStorage
import Monaco as Monaco
import Prelude (bind, bottom, const, map, not, show, unit, ($), (<$>), (<<<), (<>), (==))
import StaticData as StaticData
import Text.Pretty (pretty)
import Types (Action(..), ChildSlots, FrontendState, JSCompilationState(..), _jsCompilationResult, _jsEditorKeybindings, _jsEditorSlot, _showBottomPanel)

render ::
  forall m.
  MonadAff m =>
  FrontendState ->
  ComponentHTML Action ChildSlots m
render state =
  div_
    [ section [ class_ (ClassName "code-panel") ]
        [ div [ classes (codeEditor $ state ^. _showBottomPanel) ]
            [ jsEditor state ]
        ]
    , bottomPanel state
    ]

otherActions :: forall p. FrontendState -> HTML p Action
otherActions state =
  div [ classes [ ClassName "group" ] ]
    [ editorOptions state
    , compileButton state
    , sendButton state
    ]

sendButton :: forall p. FrontendState -> HTML p Action
sendButton state = case view _jsCompilationResult state of
  JSCompiledSuccessfully _ -> button [ onClick $ const $ Just SendResultJSToSimulator ] [ text "Send To Simulator" ]
  _ -> text ""

editorOptions :: forall p. FrontendState -> HTML p Action
editorOptions state =
  div [ class_ (ClassName "editor-options") ]
    [ select
        [ HTML.id_ "editor-options"
        , class_ (ClassName "dropdown-header")
        , onSelectedIndexChange (\idx -> JSSelectEditorKeyBindings <$> toEnum idx)
        ]
        (map keybindingItem (upFromIncluding bottom))
    ]
  where
  keybindingItem item =
    if state ^. _jsEditorKeybindings == item then
      option [ class_ (ClassName "selected-item"), HTML.value (show item) ] [ text $ show item ]
    else
      option [ HTML.value (show item) ] [ text $ show item ]

jsEditor ::
  forall m.
  MonadAff m =>
  FrontendState ->
  ComponentHTML Action ChildSlots m
jsEditor state = slot _jsEditorSlot unit component unit (Just <<< JSHandleEditorMessage)
  where
  setup editor =
    liftEffect do
      mContents <- LocalStorage.getItem StaticData.jsBufferLocalStorageKey
      let
        contents = fromMaybe JSE.escrow mContents
      model <- Monaco.getModel editor
      Monaco.setValue model contents

  component = monacoComponent $ JSM.settings setup

bottomPanel :: forall p. FrontendState -> HTML p Action
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

compileButton :: forall p. FrontendState -> HTML p Action
compileButton state =
  button [ onClick $ const $ Just CompileJSProgram ]
    [ text (if state ^. _jsCompilationResult <<< to isLoading then "Compiling..." else "Compile") ]
  where
  isLoading JSCompiling = true

  isLoading _ = false

resultPane :: forall p. FrontendState -> Array (HTML p Action)
resultPane state =
  if state ^. _showBottomPanel then case view _jsCompilationResult state of
    JSCompiledSuccessfully (InterpreterResult result) ->
      [ div [ classes [ ClassName "code-editor", ClassName "expanded", ClassName "code" ] ]
          numberedText
      ]
      where
      numberedText = (code_ <<< Array.singleton <<< text) <$> split (Pattern "\n") ((show <<< pretty <<< _.result) result)
    JSCompilationError err -> [ compilationErrorPane err ]
    _ -> [ text "" ]
  else
    [ text "" ]

compilationErrorPane :: forall p. CompilationError -> HTML p Action
compilationErrorPane (RawError error) = div_ [ text "There was an error when running the JavaScript code:", code_ [ pre_ [ text $ error ] ] ]

compilationErrorPane (JSONParsingError error) = div_ [ text "There was an error when parsing the resulting JSON:", code_ [ pre_ [ text $ error ] ], text "Please, use the JS API provided (see tutorial and examples). If you did use the JS API and still get this error, kindly report the problem at ", a [ href "https://github.com/input-output-hk/plutus/issues/new" ] [ text "https://github.com/input-output-hk/plutus/issues/new" ], text " including the code that caused the error. Thank you" ]

compilationErrorPane (CompilationError error) =
  div
    [ class_ $ ClassName "compilation-error"
    ]
    [ text $ "There is a syntax error in line " <> show error.row <> ", column " <> show error.column <> ":"
    , code_ [ pre_ [ text $ String.joinWith "\n" error.text ] ]
    ]
