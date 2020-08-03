module HaskellEditor where

import Data.Array as Array
import Data.Either (Either(..))
import Data.Enum (toEnum, upFromIncluding)
import Data.Json.JsonEither (JsonEither(..))
import Data.Lens (to, view, (^.))
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.String (Pattern(..), split)
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Examples.Haskell.Contracts as HE
import Halogen (ClassName(..), ComponentHTML, liftEffect)
import Halogen.Classes (aHorizontal, activeClasses, analysisPanel, closeDrawerArrowIcon, codeEditor, footerPanelBg, jFlexStart, minimizeIcon, panelSubHeader, panelSubHeaderMain, spaceLeft)
import Halogen.HTML (HTML, a, button, code_, div, div_, img, li, option, pre_, section, select, slot, small_, text, ul)
import Halogen.HTML.Events (onClick, onSelectedIndexChange)
import Halogen.HTML.Properties (alt, class_, classes, disabled, src)
import Halogen.HTML.Properties as HTML
import Halogen.Monaco (monacoComponent)
import Language.Haskell.Interpreter (CompilationError(..), InterpreterError(..), InterpreterResult(..))
import Language.Haskell.Monaco as HM
import LocalStorage as LocalStorage
import Monaco as Monaco
import Network.RemoteData (RemoteData(..), isLoading, isSuccess)
import Prelude (bind, bottom, const, eq, map, not, show, unit, ($), (<$>), (<<<), (<>), (==), (||))
import StaticData as StaticData
import Types (ChildSlots, FrontendState, HAction(..), _activeHaskellDemo, _compilationResult, _haskellEditorKeybindings, _haskellEditorSlot, _showBottomPanel, bottomPanelHeight)

render ::
  forall m.
  MonadAff m =>
  FrontendState ->
  Array (ComponentHTML HAction ChildSlots m)
render state =
  [ section [ classes [ panelSubHeader, aHorizontal ] ]
      [ div [ classes [ panelSubHeaderMain, aHorizontal ] ]
          [ div [ classes [ ClassName "demo-title", aHorizontal, jFlexStart ] ]
              [ div [ classes [ ClassName "demos", spaceLeft ] ]
                  [ small_ [ text "Demos:" ]
                  ]
              ]
          , ul [ classes [ ClassName "demo-list", aHorizontal ] ]
              (demoScriptLink <$> Array.fromFoldable (Map.keys StaticData.demoFiles))
          ]
      , div [ class_ (ClassName "editor-options") ]
          [ select
              [ HTML.id_ "editor-options"
              , class_ (ClassName "dropdown-header")
              , onSelectedIndexChange (\idx -> HaskellSelectEditorKeyBindings <$> toEnum idx)
              ]
              (map keybindingItem (upFromIncluding bottom))
          ]
      ]
  , section [ class_ (ClassName "code-panel") ]
      [ div [ classes (codeEditor $ state ^. _showBottomPanel) ]
          [ haskellEditor state ]
      ]
  ]
  where
  keybindingItem item =
    if state ^. _haskellEditorKeybindings == item then
      option [ class_ (ClassName "selected-item"), HTML.value (show item) ] [ text $ show item ]
    else
      option [ HTML.value (show item) ] [ text $ show item ]

  demoScriptLink key = li [ state ^. _activeHaskellDemo <<< activeClasses (eq key) ] [ a [ onClick $ const $ Just $ LoadHaskellScript key ] [ text key ] ]

haskellEditor ::
  forall m.
  MonadAff m =>
  FrontendState ->
  ComponentHTML HAction ChildSlots m
haskellEditor state = slot _haskellEditorSlot unit component unit (Just <<< HaskellHandleEditorMessage)
  where
  setup editor =
    liftEffect do
      mContents <- LocalStorage.getItem StaticData.bufferLocalStorageKey
      let
        contents = fromMaybe HE.escrow mContents
      model <- Monaco.getModel editor
      Monaco.setValue model contents

  component = monacoComponent $ HM.settings setup

bottomPanel :: forall p. FrontendState -> HTML p HAction
bottomPanel state =
  div ([ classes [ analysisPanel ], bottomPanelHeight (state ^. _showBottomPanel) ])
    [ div
        [ classes [ footerPanelBg, ClassName "flip-x" ] ]
        [ section [ classes [ ClassName "panel-header", aHorizontal ] ]
            [ div [ classes [ ClassName "panel-sub-header-main", aHorizontal ] ]
                [ div [ class_ (ClassName "minimize-icon-container") ]
                    [ a [ onClick $ const $ Just $ ShowBottomPanel (state ^. _showBottomPanel <<< to not) ]
                        [ img [ classes (minimizeIcon $ state ^. _showBottomPanel), src closeDrawerArrowIcon, alt "close drawer icon" ] ]
                    ]
                , div
                    [ classes ([ ClassName "panel-tab", aHorizontal, ClassName "haskell-buttons" ])
                    ]
                    [ button [ onClick $ const $ Just CompileHaskellProgram ] [ text (if state ^. _compilationResult <<< to isLoading then "Compiling..." else "Compile") ]
                    , sendResultButton state "Send To Simulator" SendResultToSimulator
                    , sendResultButton state "Send To Blockly" SendResultToBlockly
                    ]
                ]
            ]
        , section
            [ classes [ ClassName "panel-sub-header", aHorizontal, ClassName "panel-contents" ]
            ]
            (resultPane state)
        ]
    ]

sendResultButton :: forall p. FrontendState -> String -> HAction -> HTML p HAction
sendResultButton state msg action =
  let
    compilationResult = view _compilationResult state
  in
    case view _compilationResult state of
      Success (JsonEither (Right (InterpreterResult result))) ->
        button
          [ onClick $ const $ Just action
          , disabled (isLoading compilationResult || (not isSuccess) compilationResult)
          ]
          [ text msg ]
      _ -> text ""

resultPane :: forall p. FrontendState -> Array (HTML p HAction)
resultPane state =
  if state ^. _showBottomPanel then case view _compilationResult state of
    Success (JsonEither (Right (InterpreterResult result))) ->
      [ div [ classes [ ClassName "code-editor", ClassName "expanded", ClassName "code" ] ]
          numberedText
      ]
      -- [ code_
      --     [ pre [ class_ $ ClassName "success-code" ] [ text (unwrap result.result) ]
      --     ]
      -- ]
      where
      numberedText = (code_ <<< Array.singleton <<< text) <$> split (Pattern "\n") (unwrap result.result)
    Success (JsonEither (Left (TimeoutError error))) -> [ text error ]
    Success (JsonEither (Left (CompilationErrors errors))) -> map compilationErrorPane errors
    _ -> [ text "" ]
  else
    [ text "" ]

compilationErrorPane :: forall p. CompilationError -> HTML p HAction
compilationErrorPane (RawError error) = div_ [ text error ]

compilationErrorPane (CompilationError error) =
  div
    [ class_ $ ClassName "compilation-error"
    ]
    [ text $ "Line " <> show error.row <> ", Column " <> show error.column <> ":"
    , code_ [ pre_ [ text $ String.joinWith "\n" error.text ] ]
    ]
