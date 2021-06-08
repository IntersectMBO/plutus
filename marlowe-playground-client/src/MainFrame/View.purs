module MainFrame.View where

import Prelude hiding (div)
import Auth (_GithubUser, authStatusAuthRole)
import BlocklyEditor.View as BlocklyEditor
import Data.Lens (has, to, (^.))
import Data.Maybe (Maybe(..), isNothing)
import Effect.Aff.Class (class MonadAff)
import Gists.Types (GistAction(..))
import Halogen (ComponentHTML)
import Halogen.ActusBlockly as ActusBlockly
import Halogen.Classes (marlowePlayLogo)
import Halogen.Css (classNames)
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (HTML, a, div, div_, footer, h1, header, img, main, section, slot, span, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (href, id_, src, target)
import HaskellEditor.View (otherActions, render) as HaskellEditor
import Home as Home
import Icons (Icon(..), icon)
import JavascriptEditor.View as JSEditor
import MainFrame.Types (Action(..), ChildSlots, ModalView(..), State, View(..), _actusBlocklySlot, _authStatus, _blocklyEditorState, _contractMetadata, _createGistResult, _gistId, _hasUnsavedChanges, _haskellState, _javascriptState, _marloweEditorState, _projectName, _simulationState, _view, hasGlobalLoading)
import Marlowe.ActusBlockly as AMB
import MarloweEditor.View as MarloweEditor
import Modal.View (modal)
import Network.RemoteData (_Loading, _Success)
import SimulationPage.View as Simulation

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div [ classNames [ "site-wrap" ] ]
    ( [ header [ classNames [ "no-margins", "flex", "flex-col" ] ]
          [ div [ classNames [ "flex", "items-center", "justify-between", "bg-gray-dark", "px-medium", "py-small" ] ]
              [ img
                  [ classNames [ "h-10", "cursor-pointer" ]
                  , onClick $ const $ Just $ ChangeView HomePage
                  , src marlowePlayLogo
                  ]
              , projectTitle
              , div_
                  [ a [ href "./doc/marlowe/tutorials/index.html", target "_blank", classNames [ "font-semibold" ] ] [ text "Tutorial" ]
                  , a [ onClick $ const $ Just $ ChangeView ActusBlocklyEditor, classNames [ "ml-medium", "font-semibold" ] ] [ text "Actus Labs" ]
                  ]
              ]
          , topBar
          ]
      , main []
          [ section [ id_ "main-panel" ]
              [ tabContents HomePage [ Home.render state ]
              , tabContents Simulation [ renderSubmodule _simulationState SimulationAction (Simulation.render (state ^. _contractMetadata)) state ]
              , tabContents MarloweEditor [ renderSubmodule _marloweEditorState MarloweEditorAction (MarloweEditor.render (state ^. _contractMetadata)) state ]
              , tabContents HaskellEditor [ renderSubmodule _haskellState HaskellAction (HaskellEditor.render (state ^. _contractMetadata)) state ]
              , tabContents JSEditor [ renderSubmodule _javascriptState JavascriptAction (JSEditor.render (state ^. _contractMetadata)) state ]
              , tabContents BlocklyEditor [ renderSubmodule _blocklyEditorState BlocklyEditorAction (BlocklyEditor.render (state ^. _contractMetadata)) state ]
              , tabContents ActusBlocklyEditor
                  [ slot _actusBlocklySlot unit (ActusBlockly.blockly AMB.rootBlockName AMB.blockDefinitions AMB.toolbox) unit (Just <<< HandleActusBlocklyMessage)
                  , AMB.workspaceBlocks
                  ]
              ]
          ]
      , modal state
      , globalLoadingOverlay
      , footer [ classNames [ "flex", "justify-between", "px-medium", "py-small", "bg-gray-dark", "font-semibold" ] ]
          [ div [ classNames [ "flex" ] ]
              [ a [ href "https://cardano.org/", target "_blank", classNames [ "pr-small" ] ] [ text "cardano.org" ]
              , a [ href "https://iohk.io/", target "_blank", classNames [ "pl-small" ] ] [ text "iohk.io" ]
              ]
          , div_ [ text (copyright <> " 2021 IOHK Ltd") ]
          , div [ classNames [ "flex" ] ]
              [ a [ href "https://t.me/IOHK_Marlowe", target "_blank", classNames [ "pr-small" ] ] [ text "Telegram" ]
              , a [ href "https://twitter.com/hashtag/Marlowe", target "_blank", classNames [ "pl-small" ] ] [ text "Twitter" ]
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

        spinner = if isLoading then icon Spinner else div [ classNames [ "empty" ] ] []
      in
        div [ classNames [ "project-title" ] ]
          [ h1 [ classNames [ "text-lg" ] ]
              {- TODO: Fix style when name is super long -}
              [ text title
              , span [ classNames [ "unsave-change-indicator" ] ] [ text unsavedChangesIndicator ]
              ]
          , spinner
          ]

  isActiveView activeView = state ^. _view <<< to (eq activeView)

  tabContents activeView contents =
    div
      [ classNames $ if isActiveView activeView then [ "h-full" ] else [ "hidden" ]
      ]
      contents

  topBar =
    if showtopBar then
      div
        [ classNames [ "global-actions" ] ]
        ([ menuBar state ] <> otherActions (state ^. _view))
    else
      div_ []

  showtopBar = case state ^. _view of
    HaskellEditor -> true
    JSEditor -> true
    BlocklyEditor -> true
    ActusBlocklyEditor -> true
    Simulation -> true
    MarloweEditor -> true
    _ -> false

  otherActions HaskellEditor = [ renderSubmodule _haskellState HaskellAction HaskellEditor.otherActions state ]

  otherActions Simulation = [ renderSubmodule _simulationState SimulationAction Simulation.otherActions state ]

  otherActions JSEditor = [ renderSubmodule _javascriptState JavascriptAction JSEditor.otherActions state ]

  otherActions MarloweEditor = [ renderSubmodule _marloweEditorState MarloweEditorAction MarloweEditor.otherActions state ]

  otherActions BlocklyEditor = [ renderSubmodule _blocklyEditorState BlocklyEditorAction BlocklyEditor.otherActions state ]

  otherActions _ = []

  globalLoadingOverlay =
    if hasGlobalLoading state then
      div [ classNames [ "loading-overlay", "text-3xl", "font-semibold", "text-white" ] ]
        [ div [ classNames [ "mb-small" ] ] [ text "Loading..." ]
        , div_ [ icon Spinner ]
        ]
    else
      text ""

menuBar :: forall p. State -> HTML p Action
menuBar state =
  div [ classNames [ "menu-bar" ] ]
    [ menuButton (OpenModal NewProject) "New Project"
    , gistModal (OpenModal OpenProject) "Open"
    , menuButton (OpenModal OpenDemo) "Open Example"
    , menuButton (OpenModal RenameProject) "Rename"
    , gistModal (if isNothing $ state ^. _gistId then OpenModal SaveProjectAs else GistAction PublishOrUpdateGist) "Save"
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
