module MainFrame.View where

import Prelude hiding (div)
import Auth (_GithubUser, authStatusAuthRole)
import BlocklyEditor.View as BlocklyEditor
import Data.Lens (has, to, (^.))
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Gists.Types (GistAction(..))
import Halogen (ComponentHTML)
import Halogen.ActusBlockly as ActusBlockly
import Halogen.Classes (aHorizontal, active, flex, fontSemibold, fullHeight, fullWidth, group, hide, noMargins, smallSpaceBottom, spaceLeft, spaceRight, text3xl, textWhite, uppercase, vl)
import Halogen.Classes as Classes
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (ClassName(ClassName), HTML, a, div, div_, h1_, h2, header, hr_, main, section, slot, span, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, href, id_, target)
import Halogen.SVG (GradientUnits(..), Translate(..), d, defs, gradientUnits, linearGradient, offset, path, stop, stopColour, svg, transform, x1, x2, y2)
import Halogen.SVG as SVG
import HaskellEditor.View (otherActions, render) as HaskellEditor
import Home as Home
import Icons (Icon(..), icon)
import JavascriptEditor.View as JSEditor
import MainFrame.Types (Action(..), ChildSlots, ModalView(..), State, View(..), _actusBlocklySlot, _authStatus, _blocklyEditorState, _createGistResult, _hasUnsavedChanges, _haskellState, _javascriptState, _marloweEditorState, _projectName, _simulationState, _view, _walletSlot, hasGlobalLoading)
import Marlowe (SPParams_)
import Marlowe.ActusBlockly as AMB
import MarloweEditor.View as MarloweEditor
import Modal.View (modal)
import Network.RemoteData (_Loading, _Success)
import Servant.PureScript.Settings (SPSettings_)
import SimulationPage.View as Simulation
import Wallet as Wallet

render ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  State ->
  ComponentHTML Action ChildSlots m
render settings state =
  div [ class_ (ClassName "site-wrap") ]
    ( [ header [ classes [ noMargins, aHorizontal ] ]
          [ div [ classes [ aHorizontal, fullWidth ] ]
              [ div [ classes [ group, aHorizontal, ClassName "marlowe-title-group" ] ]
                  [ div [ class_ (ClassName "marlowe-logo"), onClick $ const $ Just $ ChangeView HomePage ] [ marloweIcon ]
                  , h2 [ classes [ spaceLeft, uppercase, spaceRight ] ] [ text "Marlowe Playground" ]
                  ]
              , projectTitle
              , div [ classes [ group, ClassName "marlowe-links-group" ] ]
                  [ a [ href "./tutorial/index.html", target "_blank", classes [ ClassName "external-links" ] ] [ text "Tutorial" ]
                  , a [ onClick $ const $ Just $ ChangeView ActusBlocklyEditor, classes [ ClassName "external-links" ] ] [ text "Actus Labs" ]
                  ]
              ]
          ]
      , main []
          [ topBar
          , hr_
          , section [ id_ "main-panel" ]
              [ tabContents HomePage [ Home.render state ]
              , tabContents Simulation [ renderSubmodule _simulationState SimulationAction Simulation.render state ]
              , tabContents MarloweEditor [ renderSubmodule _marloweEditorState MarloweEditorAction MarloweEditor.render state ]
              , tabContents HaskellEditor [ renderSubmodule _haskellState HaskellAction HaskellEditor.render state ]
              , tabContents JSEditor [ renderSubmodule _javascriptState JavascriptAction JSEditor.render state ]
              , tabContents BlocklyEditor [ renderSubmodule _blocklyEditorState BlocklyEditorAction BlocklyEditor.render state ]
              , tabContents ActusBlocklyEditor
                  [ slot _actusBlocklySlot unit (ActusBlockly.blockly AMB.rootBlockName AMB.blockDefinitions) unit (Just <<< HandleActusBlocklyMessage)
                  , AMB.toolbox
                  , AMB.workspaceBlocks
                  ]
              , tabContents WalletEmulator
                  [ div [ classes [ ClassName "full-height" ] ]
                      [ slot _walletSlot unit Wallet.mkComponent unit (Just <<< HandleWalletMessage) ]
                  ]
              ]
          ]
      , modal state
      , globalLoadingOverlay
      , div [ classes [ ClassName "footer" ] ]
          [ div [ classes [ flex, ClassName "links" ] ]
              [ a [ href "https://cardano.org/", target "_blank" ] [ text "cardano.org" ]
              , vl
              , a [ href "https://iohk.io/", target "_blank" ] [ text "iohk.io" ]
              ]
          , div [] [ text (copyright <> " 2020 IOHK Ltd") ]
          , div [ classes [ flex, ClassName "links" ] ]
              [ a [ href "https://t.me/IOHK_Marlowe", target "_blank" ] [ text "Telegram" ]
              , vl
              , a [ href "https://twitter.com/hashtag/Marlowe", target "_blank" ] [ text "Twitter" ]
              ]
          ]
      ]
    )
  where
  copyright = "\x00A9"

  projectTitle = case state ^. _view of
    HomePage -> text ""
    _ ->
      let
        title = state ^. _projectName

        unsavedChangesIndicator = if state ^. _hasUnsavedChanges then "*" else ""

        isLoading = has (_createGistResult <<< _Loading) state

        spinner = if isLoading then icon Spinner else div [ classes [ ClassName "empty" ] ] []
      in
        div [ classes [ ClassName "project-title" ] ]
          [ h1_
              {- TODO: Fix style when name is super long -}
              [ text title
              , span [ class_ (ClassName "unsave-change-indicator") ] [ text unsavedChangesIndicator ]
              ]
          , spinner
          ]

  isActiveView activeView = state ^. _view <<< to (eq activeView)

  isActiveTab activeView = if isActiveView activeView then [ active ] else []

  tabContents activeView contents = if isActiveView activeView then div [ classes [ fullHeight, Classes.scroll ] ] contents else div [ classes [ hide ] ] contents

  topBar = div [ class_ (ClassName "global-actions") ] ([ menuBar state ] <> otherActions (state ^. _view))

  otherActions HaskellEditor = [ renderSubmodule _haskellState HaskellAction HaskellEditor.otherActions state ]

  otherActions Simulation = [ renderSubmodule _simulationState SimulationAction Simulation.otherActions state ]

  otherActions JSEditor = [ renderSubmodule _javascriptState JavascriptAction JSEditor.otherActions state ]

  otherActions MarloweEditor = [ renderSubmodule _marloweEditorState MarloweEditorAction MarloweEditor.otherActions state ]

  otherActions BlocklyEditor = [ renderSubmodule _blocklyEditorState BlocklyEditorAction BlocklyEditor.otherActions state ]

  otherActions _ = []

  globalLoadingOverlay =
    if hasGlobalLoading state then
      div [ classes [ ClassName "loading-overlay", text3xl, fontSemibold, textWhite ] ]
        [ div [ class_ smallSpaceBottom ] [ text "Loading..." ]
        , div_ [ icon Spinner ]
        ]
    else
      text ""

menuBar :: forall p. State -> HTML p Action
menuBar state =
  div [ classes [ ClassName "menu-bar" ] ]
    $ [ menuButton (OpenModal NewProject) "New Project"
      , gistModal (OpenModal OpenProject) "Open"
      , menuButton (OpenModal OpenDemo) "Open Example"
      ]
    <> showInEditor
        [ menuButton (OpenModal RenameProject) "Rename"
        , gistModal (GistAction PublishGist) "Save"
        , gistModal (OpenModal SaveProjectAs) "Save As..."
        ]
  where
  menuButton action name =
    a [ onClick $ const $ Just action ]
      [ span [] [ text name ]
      ]

  gistModal action name =
    if has (_authStatus <<< _Success <<< authStatusAuthRole <<< _GithubUser) state then
      menuButton action name
    else
      menuButton (OpenModal $ GithubLogin action) name

  -- Even if we end up writting more by selecting the cases in which the buttons should
  -- appear, I prefer this to selecting which views we shouldn't show the buttons. The
  -- reason is that if we add a new view, we don't need to adjust this.
  -- TODO: Check if we should show the buttons for WalletEmulator and ActusBlocklyEditor
  showInEditor buttons = case state ^. _view of
    HaskellEditor -> buttons
    JSEditor -> buttons
    BlocklyEditor -> buttons
    ActusBlocklyEditor -> buttons
    Simulation -> buttons
    MarloweEditor -> buttons
    _ -> []

marloweIcon :: forall p a. HTML p a
marloweIcon =
  svg [ SVG.width (SVG.Length 35.0), SVG.height (SVG.Length 26.0), SVG.viewBox (SVG.Box { x: 0, y: 0, width: 60, height: 42 }) ]
    [ defs []
        [ linearGradient [ id_ "marlowe__linear-gradient", x1 (SVG.Length 0.5), x2 (SVG.Length 0.5), y2 (SVG.Length 1.0), gradientUnits ObjectBoundingBox ]
            [ stop [ offset (SVG.Length 0.221), stopColour "#832dc4" ] []
            , stop [ offset (SVG.Length 0.377), stopColour "#5e35b8" ] []
            , stop [ offset (SVG.Length 0.543), stopColour "#3f3dad" ] []
            , stop [ offset (SVG.Length 0.704), stopColour "#2942a6" ] []
            , stop [ offset (SVG.Length 0.857), stopColour "#1c45a2" ] []
            , stop [ offset (SVG.Length 0.994), stopColour "#1746a0" ] []
            ]
        ]
    , path
        [ id_ "prefix__marlowe-logo"
        , d "M90.464 35.544c1.02 0 2.232.024 2.736.072V30.4a42.042 42.042 0 00-30.06 10.124c-8.88-7.68-20.784-10.992-29.916-9.96v4.884c.516-.036 1.308-.06 2.208-.06h.048l.156-.012.2.012a19.663 19.663 0 012.264.112h.1c12.324 1.488 21.984 7.212 28.7 17.556a236 236 0 00-3.792 6.3c-.756-1.236-2.832-5.04-3.672-6.444a44.98 44.98 0 012.028-3.06c-1.284-1.26-2.484-2.4-3.732-3.588-.9 1.116-1.62 1.992-2.412 2.964-3.36-2.28-6.576-4.476-10.392-5.628A29.291 29.291 0 0033.2 42.228v29.688h4.98V47.424c5.028.876 10.332 2.736 14.472 6.672a46.733 46.733 0 00-3.9 17.832h5.172a34.82 34.82 0 012.628-13.644 43.568 43.568 0 013.24 7.884 44.62 44.62 0 01.864 5.736h2.3v-8.268h.072a.77.77 0 11.84-.768.759.759 0 01-.684.768h.072V71.9h-.3l.072.012h.228V71.9h2.4a24.792 24.792 0 014.128-13.728 42.589 42.589 0 012.7 13.74h5.296c0-5.088-1.992-14.6-4.092-18.552a22.176 22.176 0 0114.244-5.616c0 4-.012 8 0 12.012.012 4.032-.084 8.076.072 12.144h5.2V42.144a35.632 35.632 0 00-12.012 1.512 33.507 33.507 0 00-10.468 5.664c-1.092-1.9-2.316-3.432-3.564-5.244a37.471 37.471 0 0120.892-8.46c.504-.048 1.392-.072 2.412-.072z"
        , transform (Translate { x: (negate 33.2), y: (negate 30.301) })
        ]
        []
    ]
