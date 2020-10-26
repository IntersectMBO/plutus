module MainFrame.View where

import Auth (_GithubUser, authStatusAuthRole)
import Data.Lens (has, to, (^.))
import Data.Maybe (Maybe(..))
import Demos.View (render) as Demos
import Effect.Aff.Class (class MonadAff)
import GistButtons (authButton)
import Gists (GistAction(..))
import Halogen (ComponentHTML)
import Halogen.ActusBlockly as ActusBlockly
import Halogen.Blockly (blockly)
import Halogen.Classes (aHorizontal, active, fullHeight, fullWidth, hide, noMargins, spaceLeft, spaceRight, uppercase)
import Halogen.Classes as Classes
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (ClassName(ClassName), HTML, a, button, div, h1_, h2, header, main, section, slot, span, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, href, id_, target)
import Halogen.SVG (GradientUnits(..), Translate(..), d, defs, gradientUnits, linearGradient, offset, path, stop, stopColour, svg, transform, x1, x2, y2)
import Halogen.SVG as SVG
import HaskellEditor.View (otherActions, render) as HaskellEditor
import Home as Home
import Icons (Icon(..), icon)
import JSEditor as JSEditor
import MainFrame.Types (Action(..), ChildSlots, State, ModalView(..), View(..), _actusBlocklySlot, _authStatus, _blocklySlot, _createGistResult, _haskellState, _newProject, _projectName, _projects, _rename, _saveAs, _showModal, _simulationState, _view, _walletSlot)
import Marlowe (SPParams_)
import Marlowe.ActusBlockly as AMB
import Marlowe.Blockly as MB
import Network.RemoteData (_Loading, _Success)
import NewProject.State (render) as NewProject
import Prelude (const, eq, identity, negate, unit, ($), (<<<), (<>))
import Projects.State (render) as Projects
import Rename.State (render) as Rename
import SaveAs.State (render) as SaveAs
import Servant.PureScript.Settings (SPSettings_)
import Simulation as Simulation
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
              [ div [ classes [ ClassName "group", aHorizontal, ClassName "marlowe-title-group" ] ]
                  [ div [ class_ (ClassName "marlowe-logo"), onClick $ const $ Just $ ChangeView HomePage ] [ marloweIcon ]
                  , h2 [ classes [ spaceLeft, uppercase, spaceRight ] ] [ text "Marlowe Playground" ]
                  ]
              , projectTitle
              , div [ classes [ ClassName "group", ClassName "marlowe-links-group" ] ]
                  [ a [ href "./tutorial/index.html", target "_blank", classes [ ClassName "external-links" ] ] [ text "Tutorial" ]
                  , a [ onClick $ const $ Just $ ChangeView ActusBlocklyEditor, classes [ ClassName "external-links" ] ] [ text "Actus Labs" ]
                  ]
              ]
          ]
      , main []
          [ topBar
          , section [ id_ "main-panel" ]
              [ tabContents HomePage [ Home.render state ]
              , tabContents Simulation [ renderSubmodule _simulationState SimulationAction Simulation.render state ]
              , tabContents HaskellEditor [ renderSubmodule _haskellState HaskellAction HaskellEditor.render state ]
              , tabContents JSEditor [ JSEditor.render state ]
              , tabContents BlocklyEditor
                  [ slot _blocklySlot unit (blockly MB.rootBlockName MB.blockDefinitions) unit (Just <<< HandleBlocklyMessage)
                  , MB.toolbox
                  , MB.workspaceBlocks
                  ]
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
      ]
    )
  where
  projectTitle =
    let
      title = state ^. _projectName

      isLoading = has (_createGistResult <<< _Loading) state

      spinner = if isLoading then icon Spinner else div [ classes [ ClassName "empty" ] ] []
    in
      div [ classes [ ClassName "project-title" ] ] [ h1_ [ text title ], spinner ]

  isActiveView activeView = state ^. _view <<< to (eq activeView)

  isActiveTab activeView = if isActiveView activeView then [ active ] else []

  tabContents activeView contents = if isActiveView activeView then div [ classes [ fullHeight, Classes.scroll ] ] contents else div [ classes [ hide ] ] contents

  topBar = div [ class_ (ClassName "global-actions") ] ([ menuBar state ] <> otherActions (state ^. _view))

  otherActions HaskellEditor = [ renderSubmodule _haskellState HaskellAction HaskellEditor.otherActions state ]

  otherActions Simulation = [ renderSubmodule _simulationState SimulationAction Simulation.otherActions state ]

  otherActions JSEditor = [ JSEditor.otherActions state ]

  otherActions BlocklyEditor =
    [ div [ classes [ ClassName "group" ] ]
        [ button
            [ onClick $ const $ Just SendBlocklyToSimulator
            ]
            [ text "Send To Simulator" ]
        ]
    ]

  otherActions _ = []

modal ::
  forall m.
  MonadAff m =>
  State -> ComponentHTML Action ChildSlots m
modal state = case state ^. _showModal of
  Nothing -> text ""
  Just view ->
    div [ classes [ ClassName "modal" ] ]
      [ div [ classes [ ClassName "modal-container" ] ]
          [ div [ classes [ ClassName "modal-content" ] ]
              [ a [ class_ (ClassName "close"), onClick $ const $ Just CloseModal ] [ text "x" ]
              , modalContent view
              ]
          ]
      ]
  where
  modalContent NewProject = renderSubmodule _newProject NewProjectAction NewProject.render state

  modalContent OpenProject = renderSubmodule _projects ProjectsAction Projects.render state

  modalContent OpenDemo = renderSubmodule identity DemosAction Demos.render state

  modalContent RenameProject = renderSubmodule _rename RenameAction Rename.render state

  modalContent SaveProjectAs = renderSubmodule _saveAs SaveAsAction SaveAs.render state

  modalContent GithubLogin = authButton state

menuBar :: forall p. State -> HTML p Action
menuBar state =
  div [ classes [ ClassName "menu-bar" ] ]
    [ menuButton (OpenModal NewProject) "New" "New Project"
    , gistModal (OpenModal OpenProject) "Open" "Open Project"
    , menuButton (OpenModal OpenDemo) "Open Example" "Open Example"
    , menuButton (OpenModal RenameProject) "Rename" "Rename Project"
    , gistModal (GistAction PublishGist) "Save" "Save Project"
    , gistModal (OpenModal SaveProjectAs) "Save As" "Save As New Project"
    ]
  where
  menuButton action shortName longName =
    a [ onClick $ const $ Just action ]
      [ span [ class_ (ClassName "short-text") ] [ text shortName ]
      , span [ class_ (ClassName "long-text") ] [ text longName ]
      ]

  gistModal action shortName restOfName =
    if has (_authStatus <<< _Success <<< authStatusAuthRole <<< _GithubUser) state then
      menuButton action shortName restOfName
    else
      menuButton (OpenModal GithubLogin) shortName restOfName

marloweIcon :: forall p a. HTML p a
marloweIcon =
  svg [ SVG.width (SVG.Length 50.0), SVG.height (SVG.Length 41.628), SVG.viewBox (SVG.Box { x: 0, y: 0, width: 60, height: 42 }) ]
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
