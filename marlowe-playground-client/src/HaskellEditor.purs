module HaskellEditor where

import Halogen.Classes (aHorizontal, accentBorderBottom, analysisPanel, blocklyIcon, closeDrawerIcon, footerPanelBg, haskellEditor, isActiveDemo, isActiveTab, jFlexStart, minimizeIcon, noMargins, panelHeader, panelHeaderMain, panelSubHeader, panelSubHeaderMain, smallBtn, spaceLeft)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Json.JsonEither (JsonEither(..))
import Data.Lens (to, view, (^.))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.String as String
import Editor (editorView)
import Effect.Aff.Class (class MonadAff)
import Halogen (ClassName(..), ComponentHTML)
import Halogen.HTML (HTML, a, button, code_, div, div_, h4, img, li, pre, pre_, section, small_, text, ul)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Extra (mapComponent)
import Halogen.HTML.Properties (alt, class_, classes, disabled, enabled, src)
import Language.Haskell.Interpreter (CompilationError(..), InterpreterError(..), InterpreterResult(..))
import Network.RemoteData (RemoteData(..), isLoading, isSuccess)
import Prelude (const, map, not, show, ($), (<$>), (<<<), (<>), (||))
import Simulation (isContractValid)
import StaticData as StaticData
import Types (ChildSlots, FrontendState, HAction(..), View(..), _compilationResult, _editorPreferences, _haskellEditorSlot, _showBottomPanel)

render ::
  forall m.
  MonadAff m =>
  FrontendState ->
  Array (ComponentHTML HAction ChildSlots m)
render state =
  [ section [ classes [ panelHeader, aHorizontal ] ]
      [ div [ classes [ panelHeaderMain, aHorizontal, noMargins, accentBorderBottom ] ]
          [ h4 [] [ text "Marlowe Contract" ] ]
      ]
  , section [ classes [ panelSubHeader, aHorizontal ] ]
      [ div [ classes [ panelSubHeaderMain, aHorizontal ] ]
          [ div [ classes [ ClassName "demo-title", aHorizontal, jFlexStart ] ]
              [ div [ classes [ ClassName "demos", spaceLeft ] ]
                  [ small_ [ text "Demos:" ]
                  ]
              ]
          , ul [ classes [ ClassName "demo-list", aHorizontal ] ]
              (demoScriptLink <$> Array.fromFoldable (Map.keys StaticData.demoFiles))
          , div [ class_ (ClassName "code-to-blockly-wrap") ]
              [ button
                  [ class_ smallBtn
                  , onClick $ const $ Just $ SetBlocklyCode
                  , enabled (isContractValid state)
                  ]
                  [ img [ class_ (ClassName "blockly-btn-icon"), src blocklyIcon, alt "blockly logo" ] ]
              ]
          ]
      ]
  , section [ classes (haskellEditor state) ]
      [ mapComponent
          HaskellEditorAction
          $ editorView defaultContents _haskellEditorSlot StaticData.bufferLocalStorageKey editorPreferences
      ]
  ]
  where
  demoScriptLink key = li [ classes (isActiveDemo state) ] [ a [ onClick $ const $ Just $ LoadHaskellScript key ] [ text key ] ]

  editorPreferences = view _editorPreferences state

  defaultContents = Map.lookup "Escrow" StaticData.demoFiles

bottomPanel :: forall p. FrontendState -> HTML p HAction
bottomPanel state =
  div [ classes (analysisPanel state) ]
    [ div [ classes (footerPanelBg state HaskellEditor <> isActiveTab state HaskellEditor) ]
        [ section [ classes [ ClassName "panel-header", aHorizontal ] ]
            [ div [ classes [ ClassName "panel-sub-header-main", aHorizontal, accentBorderBottom ] ]
                [ div
                    [ classes ([ ClassName "panel-tab", aHorizontal, ClassName "haskell-buttons" ])
                    ]
                    [ button [ onClick $ const $ Just CompileHaskellProgram ] [ text (if state ^. _compilationResult <<< to isLoading then "Compiling..." else "Compile") ]
                    , sendResultButton state
                    ]
                , div []
                    [ a [ onClick $ const $ Just $ ShowBottomPanel (state ^. _showBottomPanel <<< to not) ]
                        [ img [ classes (minimizeIcon state), src closeDrawerIcon, alt "close drawer icon" ] ]
                    ]
                ]
            ]
        , section
            [ classes [ ClassName "panel-sub-header", aHorizontal, ClassName "panel-contents" ]
            ]
            (resultPane state)
        ]
    ]

sendResultButton :: forall p. FrontendState -> HTML p HAction
sendResultButton state =
  let
    compilationResult = view _compilationResult state
  in
    case compilationResult of
      Success (JsonEither (Right (InterpreterResult result))) ->
        button
          [ onClick $ const $ Just SendResult
          , disabled (isLoading compilationResult || (not isSuccess) compilationResult)
          ]
          [ text "Send to Simulator" ]
      _ -> text ""

resultPane :: forall p. FrontendState -> Array (HTML p HAction)
resultPane state =
  let
    compilationResult = view _compilationResult state
  in
    case compilationResult of
      Success (JsonEither (Right (InterpreterResult result))) ->
        [ code_
            [ pre [ class_ $ ClassName "success-code" ] [ text (unwrap result.result) ]
            ]
        ]
      Success (JsonEither (Left (TimeoutError error))) -> [ text error ]
      Success (JsonEither (Left (CompilationErrors errors))) -> map compilationErrorPane errors
      _ -> [ text "" ]

compilationErrorPane :: forall p. CompilationError -> HTML p HAction
compilationErrorPane (RawError error) = div_ [ text error ]

compilationErrorPane (CompilationError error) =
  div
    [ class_ $ ClassName "compilation-error"
    ]
    [ text $ "Line " <> show error.row <> ", Column " <> show error.column <> ":"
    , code_ [ pre_ [ text $ String.joinWith "\n" error.text ] ]
    ]
