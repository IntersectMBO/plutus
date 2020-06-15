module MainFrame (mkMainFrame) where

import API (_RunResult)
import Data.Bifunctor (bimap)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Json.JsonEither (_JsonEither)
import Data.Lens (_Right, assign, set, to, use, view, (^.))
import Data.Lens.Extra (peruse)
import Data.List.NonEmpty as NEL
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Halogen (Component, ComponentHTML, get, liftEffect, query)
import Halogen as H
import Halogen.Analytics (handleActionWithAnalyticsTracking)
import Halogen.Blockly (BlocklyMessage(..), blockly)
import Halogen.Blockly as Blockly
import Halogen.Classes (aCenter, aHorizontal, active, btnSecondary, flexCol, hide, iohkIcon, noMargins, spaceLeft, tabIcon, tabLink, uppercase)
import Halogen.HTML (ClassName(ClassName), HTML, a, div, h1, header, img, main, nav, p, p_, section, slot, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (alt, class_, classes, href, id_, src, target)
import Halogen.Monaco as Monaco
import Halogen.Query (HalogenM)
import Halogen.Query.HalogenM (imapState, mapAction)
import Halogen.SVG (GradientUnits(..), Translate(..), d, defs, gradientUnits, linearGradient, offset, path, stop, stopColour, svg, transform, x1, x2, y2)
import Halogen.SVG as SVG
import HaskellEditor as HaskellEditor
import HaskellEditor.Types (_compilationResult)
import HaskellEditor.Types as HE
import Language.Haskell.Interpreter (_InterpreterResult)
import Language.Haskell.Monaco as HM
import Marlowe (SPParams_)
import Marlowe.Blockly as MB
import Marlowe.Monaco as MM
import Marlowe.Parser (parseContract)
import Network.RemoteData (RemoteData(..), _Success)
import Prelude (class Functor, Unit, bind, const, discard, eq, flip, identity, map, mempty, negate, pure, show, unit, void, ($), (<<<), (<>), (>))
import Router (Route)
import Router as Router
import Routing.Duplex as RD
import Routing.Duplex as RT
import Routing.Hash as Routing
import Servant.PureScript.Settings (SPSettings_)
import Simulation as Simulation
import Simulation.State (_result)
import Simulation.Types (_marloweState)
import Simulation.Types as ST
import Text.Pretty (pretty)
import Types (ChildSlots, FrontendState(FrontendState), HAction(..), HQuery(..), Message, View(..), _blocklySlot, _haskellEditorSlot, _haskellState, _marloweEditorSlot, _showBottomPanel, _simulationState, _view, _walletSlot)
import Wallet as Wallet
import WebSocket (WebSocketResponseMessage(..))
import WebSocket.Support as WS

initialState :: FrontendState
initialState =
  FrontendState
    { view: Simulation
    , blocklyState: Nothing
    , showBottomPanel: true
    , haskellState: HE.initialState
    , simulationState: ST.mkState
    }

------------------------------------------------------------
mkMainFrame ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ -> Component HTML HQuery Unit Message m
mkMainFrame settings =
  H.mkComponent
    { initialState: const initialState
    , render: render settings
    , eval:
      H.mkEval
        { handleQuery
        , handleAction: handleActionWithAnalyticsTracking (handleAction settings)
        , receive: const Nothing
        , initialize: Just Init
        , finalize: Nothing
        }
    }

toSimulation ::
  forall m a.
  Functor m =>
  HalogenM ST.State ST.Action ChildSlots Message m a -> HalogenM FrontendState HAction ChildSlots Message m a
toSimulation halogen = do
  currentState <- get
  let
    setState = flip (set _simulationState) currentState
  let
    getState = view _simulationState
  (imapState setState getState <<< mapAction SimulationAction) halogen

toHaskellEditor ::
  forall m a.
  Functor m =>
  HalogenM HE.State HE.Action ChildSlots Message m a -> HalogenM FrontendState HAction ChildSlots Message m a
toHaskellEditor halogen = do
  currentState <- get
  let
    setState = flip (set _haskellState) currentState
  let
    getState = view _haskellState
  (imapState setState getState <<< mapAction HaskellAction) halogen

handleRoute ::
  forall m action message.
  MonadEffect m =>
  Route -> HalogenM FrontendState action ChildSlots message m Unit
handleRoute Router.Home = selectView Simulation

handleRoute Router.Simulation = selectView Simulation

handleRoute Router.HaskellEditor = selectView HaskellEditor

handleRoute Router.Blockly = selectView BlocklyEditor

handleRoute Router.Wallets = selectView WalletEmulator

handleQuery ::
  forall m a.
  Functor m =>
  MonadEffect m =>
  HQuery a ->
  HalogenM FrontendState HAction ChildSlots Message m (Maybe a)
handleQuery (ReceiveWebSocketMessage msg next) = do
  void <<< toSimulation
    $ case msg of
        WS.ReceiveMessage (Left err) -> Simulation.handleQuery (ST.WebsocketResponse (Failure (show msg)) unit)
        WS.ReceiveMessage (Right (OtherError err)) -> Simulation.handleQuery ((ST.WebsocketResponse $ Failure err) unit)
        WS.ReceiveMessage (Right (CheckForWarningsResult result)) -> Simulation.handleQuery ((ST.WebsocketResponse $ Success result) unit)
        WS.WebSocketClosed -> pure $ Just unit
  pure $ Just next

handleQuery (ChangeRoute route next) = do
  handleRoute route
  pure $ Just next

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  HAction ->
  HalogenM FrontendState HAction ChildSlots Message m Unit
handleAction _ Init = do
  hash <- liftEffect Routing.getHash
  case (RD.parse Router.route) hash of
    Right route -> handleRoute route
    Left _ -> handleRoute Router.Home

handleAction s (HaskellAction action) = do
  currentState <- get
  toHaskellEditor (HaskellEditor.handleAction s action)
  case action of
    HE.SendResultToSimulator -> do
      mContract <-
        peruse
          ( _haskellState
              <<< _compilationResult
              <<< _Success
              <<< _JsonEither
              <<< _Right
              <<< _InterpreterResult
              <<< _result
              <<< _RunResult
          )
      let
        contract = case mContract of
          Just unformatted -> case parseContract unformatted of
            Right pcon -> show $ pretty pcon
            Left _ -> unformatted
          _ -> ""
      selectView Simulation
      void $ toSimulation
        $ do
            Simulation.handleAction s (ST.SetEditorText contract)
            Simulation.handleAction s ST.ResetContract
    HE.SendResultToBlockly -> selectView BlocklyEditor
    _ -> pure unit

handleAction s (SimulationAction action) = do
  currentState <- get
  toSimulation (Simulation.handleAction s action)
  case action of
    ST.SetBlocklyCode -> do
      mSource <- query _marloweEditorSlot unit (Monaco.GetText identity)
      for_ mSource \source -> void $ query _blocklySlot unit (Blockly.SetCode source unit)
      selectView BlocklyEditor
    _ -> pure unit

handleAction _ (HandleWalletMessage Wallet.SendContractToWallet) = do
  contract <- toSimulation $ Simulation.getCurrentContract
  void $ query _walletSlot unit (Wallet.LoadContract contract unit)

handleAction _ (ChangeView view) = selectView view

handleAction _ (ShowBottomPanel val) = do
  assign _showBottomPanel val
  pure unit

handleAction s (HandleBlocklyMessage (CurrentCode code)) = do
  hasStarted <- use (_simulationState <<< _marloweState <<< to (\states -> (NEL.length states) > 1))
  if hasStarted then
    void $ query _blocklySlot unit (Blockly.SetError "You can't send new code to a running simulation. Please go to the Simulation tab and click \"reset\" first" unit)
  else do
    selectView Simulation
    void $ toSimulation $ Simulation.handleAction s (ST.SetEditorText code)

------------------------------------------------------------
selectView ::
  forall m action message.
  MonadEffect m =>
  View -> HalogenM FrontendState action ChildSlots message m Unit
selectView view = do
  let
    route = case view of
      Simulation -> Router.Simulation
      HaskellEditor -> Router.HaskellEditor
      BlocklyEditor -> Router.Blockly
      WalletEmulator -> Router.Wallets
  liftEffect $ Routing.setHash (RT.print Router.route route)
  assign _view view
  case view of
    Simulation -> do
      void $ query _marloweEditorSlot unit (Monaco.Resize unit)
      void $ query _marloweEditorSlot unit (Monaco.SetTheme MM.daylightTheme.name unit)
    HaskellEditor -> do
      void $ query _haskellEditorSlot unit (Monaco.Resize unit)
      void $ query _haskellEditorSlot unit (Monaco.SetTheme HM.daylightTheme.name unit)
    BlocklyEditor -> void $ query _blocklySlot unit (Blockly.Resize unit)
    WalletEmulator -> pure unit

render ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  FrontendState ->
  ComponentHTML HAction ChildSlots m
render settings state =
  div [ class_ (ClassName "site-wrap") ]
    [ header [ classes [ noMargins, aHorizontal ] ]
        [ div [ class_ aHorizontal ]
            [ div [ class_ (ClassName "marlowe-logo") ]
                [ svg [ SVG.width (SVG.Length 60.0), SVG.height (SVG.Length 41.628), SVG.viewBox (SVG.Box { x: 0, y: 0, width: 60, height: 42 }) ]
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
                ]
            , h1 [ classes [ spaceLeft, uppercase ] ] [ text "Marlowe Playground" ]
            ]
        , p [] [ text "Online tool for creating embedded Marlowe contracts" ]
        ]
    , main []
        [ nav [ id_ "panel-nav" ]
            [ div
                [ classes ([ tabLink, aCenter, flexCol, ClassName "simulation-tab" ] <> isActiveTab state Simulation)
                , onClick $ const $ Just $ ChangeView Simulation
                ]
                [ div [ class_ tabIcon ] []
                , div [] [ text "Simulation" ]
                ]
            , div
                [ classes ([ tabLink, aCenter, flexCol, ClassName "haskell-tab" ] <> isActiveTab state HaskellEditor)
                , onClick $ const $ Just $ ChangeView HaskellEditor
                ]
                [ div [ class_ tabIcon ] []
                , div [] [ text "Haskell Editor" ]
                ]
            , div
                [ classes ([ tabLink, aCenter, flexCol, ClassName "blockly-tab" ] <> isActiveTab state BlocklyEditor)
                , onClick $ const $ Just $ ChangeView BlocklyEditor
                ]
                [ div [ class_ tabIcon ] []
                , div [] [ text "Blockly" ]
                ]
            , div
                [ classes ([ tabLink, aCenter, flexCol, ClassName "wallet-tab" ] <> isActiveTab state WalletEmulator)
                , onClick $ const $ Just $ ChangeView WalletEmulator
                ]
                [ div [ class_ tabIcon ] []
                , div [] [ text "Wallets" ]
                ]
            , div [ class_ (ClassName "nav-bottom-links") ]
                [ a [ href "./tutorial", target "_blank", classes [ btnSecondary, aHorizontal, ClassName "open-link-icon" ] ] [ text "Tutorial" ]
                , p_ [ text "Privacy Policy" ]
                , p_
                    [ text "by "
                    , img [ src iohkIcon, alt "input output hong kong logo" ]
                    ]
                ]
            ]
        , section [ id_ "main-panel" ]
            -- simulation panel
            [ div [ classes ([ hide ] <> isActiveTab state Simulation) ]
                [ bimap (map SimulationAction) SimulationAction (Simulation.render (state ^. _simulationState)) ]
            -- haskell panel
            , div [ classes ([ hide ] <> isActiveTab state HaskellEditor) ]
                [ bimap (map HaskellAction) HaskellAction (HaskellEditor.render (state ^. _haskellState)) ]
            -- blockly panel
            , div [ classes ([ hide ] <> isActiveTab state BlocklyEditor) ]
                [ slot _blocklySlot unit (blockly MB.rootBlockName MB.blockDefinitions) unit (Just <<< HandleBlocklyMessage)
                , MB.toolbox
                , MB.workspaceBlocks
                ]
            -- wallet panel
            , div [ classes ([ hide, ClassName "full-height" ] <> isActiveTab state WalletEmulator) ]
                [ slot _walletSlot unit Wallet.mkComponent unit (Just <<< HandleWalletMessage) ]
            -- Haskell Editor bottom panel
            , bimap (map HaskellAction) HaskellAction bottomPanel
            ]
        ]
    ]
  where
  bottomPanel = case state ^. _view of
    HaskellEditor -> HaskellEditor.bottomPanel (state ^. _haskellState)
    _ -> text mempty

  isActiveTab state' activeView = if state' ^. _view <<< to (eq activeView) then [ active ] else []
