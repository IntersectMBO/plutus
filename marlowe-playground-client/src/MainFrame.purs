module MainFrame (mkMainFrame) where

import API (_RunResult)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (runReaderT)
import Data.Array (catMaybes)
import Data.Either (Either(..))
import Data.Json.JsonEither (JsonEither(..))
import Data.Lens (assign, to, use, view, (^.))
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Foreign.Class (decode)
import Foreign.JSON (parseJSON)
import Halogen (Component, ComponentHTML, liftEffect, query, request)
import Halogen as H
import Halogen.Analytics (handleActionWithAnalyticsTracking)
import Halogen.Blockly (BlocklyMessage(..), blockly)
import Halogen.Blockly as Blockly
import Halogen.Classes (aCenter, aHorizontal, active, btnSecondary, flexCol, hide, iohkIcon, noMargins, spaceLeft, tabIcon, tabLink, uppercase)
import Halogen.HTML (ClassName(ClassName), HTML, a, div, h1, header, img, main, nav, p, p_, section, slot, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (alt, class_, classes, href, id_, src, target)
import Halogen.Monaco (KeyBindings(..))
import Halogen.Monaco as Monaco
import Halogen.Query (HalogenM)
import Halogen.SVG (GradientUnits(..), Translate(..), d, defs, gradientUnits, linearGradient, offset, path, stop, stopColour, svg, transform, x1, x2, y2)
import Halogen.SVG as SVG
import HaskellEditor as HaskellEditor
import Language.Haskell.Interpreter (CompilationError(CompilationError, RawError), InterpreterError(CompilationErrors, TimeoutError), SourceCode(SourceCode), _InterpreterResult)
import Language.Haskell.Monaco as HM
import LocalStorage as LocalStorage
import Marlowe (SPParams_)
import Marlowe as Server
import Marlowe.Blockly as MB
import Marlowe.Parser (parseContract)
import Monaco (IMarkerData, markerSeverity)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Prelude (Unit, bind, const, discard, eq, flip, identity, mempty, negate, pure, show, unit, void, ($), (<$>), (<<<), (<>))
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import Simulation as Simulation
import Simulation.State (_result)
import Simulation.Types as ST
import StaticData (bufferLocalStorageKey)
import StaticData as StaticData
import Text.Pretty (pretty)
import Types (ChildSlots, FrontendState(FrontendState), HAction(..), HQuery(..), Message(..), View(..), WebData, _activeHaskellDemo, _blocklySlot, _compilationResult, _haskellEditorKeybindings, _haskellEditorSlot, _showBottomPanel, _simulationSlot, _view, _walletSlot)
import Wallet as Wallet
import WebSocket (WebSocketResponseMessage(..))

initialState :: FrontendState
initialState =
  FrontendState
    { view: Simulation
    , compilationResult: NotAsked
    , blocklyState: Nothing
    , showBottomPanel: true
    , haskellEditorKeybindings: DefaultBindings
    , activeHaskellDemo: mempty
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
        , initialize: Nothing
        , finalize: Nothing
        }
    }

handleQuery ::
  forall m a.
  HQuery a ->
  HalogenM FrontendState HAction ChildSlots Message m (Maybe a)
handleQuery (ReceiveWebsocketMessage msg next) = do
  let
    msgDecoded =
      unwrap <<< runExceptT
        $ do
            f <- parseJSON msg
            decode f
  void
    $ case msgDecoded of
        Left err -> query _simulationSlot unit (ST.WebsocketResponse (Failure (show msg)) unit)
        Right (OtherError err) -> query _simulationSlot unit ((ST.WebsocketResponse $ Failure err) unit)
        Right (CheckForWarningsResult result) -> query _simulationSlot unit ((ST.WebsocketResponse $ Success result) unit)
  pure $ Just next

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  HAction ->
  HalogenM FrontendState HAction ChildSlots Message m Unit
handleAction _ (HandleSimulationMessage (ST.BlocklyCodeSet source)) = do
  void $ query _blocklySlot unit (Blockly.SetCode source unit)
  assign _view BlocklyEditor
  void $ query _blocklySlot unit (Blockly.Resize unit)

handleAction _ (HandleSimulationMessage (ST.WebsocketMessage msg)) = H.raise (WebsocketMessage msg)

handleAction _ (HandleWalletMessage Wallet.SendContractToWallet) = do
  mContract <- query _simulationSlot unit (request ST.GetCurrentContract)
  case mContract of
    Nothing -> pure unit
    Just contract -> void $ query _walletSlot unit (Wallet.LoadContract contract unit)

handleAction _ (HaskellHandleEditorMessage (Monaco.TextChanged text)) = do
  liftEffect $ LocalStorage.setItem bufferLocalStorageKey text
  assign _activeHaskellDemo ""

handleAction _ (HaskellSelectEditorKeyBindings bindings) = do
  assign _haskellEditorKeybindings bindings
  void $ query _haskellEditorSlot unit (Monaco.SetKeyBindings bindings unit)

handleAction _ (ChangeView HaskellEditor) = selectHaskellView

handleAction _ (ChangeView Simulation) = selectSimulationView

handleAction _ (ChangeView BlocklyEditor) = do
  assign _view BlocklyEditor
  void $ query _blocklySlot unit (Blockly.Resize unit)

handleAction _ (ChangeView WalletEmulator) = selectWalletView

handleAction settings CompileHaskellProgram = do
  mContents <- query _haskellEditorSlot unit (Monaco.GetText identity)
  case mContents of
    Nothing -> pure unit
    Just contents -> do
      assign _compilationResult Loading
      result <- runAjax $ flip runReaderT settings $ (Server.postContractHaskell $ SourceCode contents)
      assign _compilationResult result
      -- Update the error display.
      let
        markers = case result of
          Success (JsonEither (Left errors)) -> toMarkers errors
          _ -> []
      void $ query _haskellEditorSlot unit (Monaco.SetModelMarkers markers identity)

handleAction _ (LoadHaskellScript key) = do
  case Map.lookup key StaticData.demoFiles of
    Nothing -> pure unit
    Just contents -> do
      void $ query _haskellEditorSlot unit (Monaco.SetText contents unit)
      assign _activeHaskellDemo key

handleAction _ SendResultToSimulator = do
  mContract <- use _compilationResult
  let
    contract = case mContract of
      Success (JsonEither (Right result)) ->
        let
          unformatted = view (_InterpreterResult <<< _result <<< _RunResult) result
        in
          case parseContract unformatted of
            Right pcon -> show $ pretty pcon
            Left _ -> unformatted
      _ -> ""
  void $ query _simulationSlot unit (ST.SetEditorText contract unit)
  void $ query _simulationSlot unit (ST.ResetContract unit)
  selectSimulationView

handleAction _ SendResultToBlockly = do
  mContract <- use _compilationResult
  case mContract of
    Success (JsonEither (Right result)) -> do
      let
        source = view (_InterpreterResult <<< _result <<< _RunResult) result
      void $ query _blocklySlot unit (Blockly.SetCode source unit)
      assign _view BlocklyEditor
      void $ query _blocklySlot unit (Blockly.Resize unit)
    _ -> pure unit

handleAction _ (ShowBottomPanel val) = do
  assign _showBottomPanel val
  void $ query _haskellEditorSlot unit (Monaco.Resize unit)
  pure unit

handleAction _ (HandleBlocklyMessage Initialized) = pure unit

handleAction _ (HandleBlocklyMessage (CurrentCode code)) = do
  mHasStarted <- query _simulationSlot unit (ST.HasStarted identity)
  let
    hasStarted = fromMaybe false mHasStarted
  if hasStarted then
    void $ query _blocklySlot unit (Blockly.SetError "You can't send new code to a running simulation. Please go to the Simulation tab and click \"reset\" first" unit)
  else do
    void $ query _simulationSlot unit (ST.SetEditorText code unit)
    selectSimulationView

------------------------------------------------------------
runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM FrontendState HAction ChildSlots Message m) a ->
  HalogenM FrontendState HAction ChildSlots Message m (WebData a)
runAjax action = RemoteData.fromEither <$> runExceptT action

selectSimulationView ::
  forall m.
  HalogenM FrontendState HAction ChildSlots Message m Unit
selectSimulationView = do
  assign _view (Simulation)
  void $ query _simulationSlot unit (ST.ResizeEditor unit)

selectHaskellView ::
  forall m.
  HalogenM FrontendState HAction ChildSlots Message m Unit
selectHaskellView = do
  assign _view (HaskellEditor)
  void $ query _haskellEditorSlot unit (Monaco.Resize unit)
  void $ query _haskellEditorSlot unit (Monaco.SetTheme HM.daylightTheme.name unit)

selectWalletView ::
  forall m.
  HalogenM FrontendState HAction ChildSlots Message m Unit
selectWalletView = assign _view WalletEmulator

toMarkers :: InterpreterError -> Array IMarkerData
toMarkers (TimeoutError _) = []

toMarkers (CompilationErrors errors) = catMaybes (toMarker <$> errors)

toMarker :: CompilationError -> Maybe IMarkerData
toMarker (RawError _) = Nothing

toMarker (CompilationError { row, column, text }) =
  Just
    { severity: markerSeverity "Error"
    , message: String.joinWith "\\n" text
    , startLineNumber: row
    , startColumn: column
    , endLineNumber: row
    , endColumn: column
    , code: mempty
    , source: mempty
    }

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
                [ slot _simulationSlot unit (Simulation.mkComponent settings) unit (Just <<< HandleSimulationMessage) ]
            -- haskell panel
            , div [ classes ([ hide ] <> isActiveTab state HaskellEditor) ]
                (HaskellEditor.render state)
            -- blockly panel
            , div [ classes ([ hide ] <> isActiveTab state BlocklyEditor) ]
                [ slot _blocklySlot unit (blockly MB.rootBlockName MB.blockDefinitions) unit (Just <<< HandleBlocklyMessage)
                , MB.toolbox
                , MB.workspaceBlocks
                ]
            -- wallet panel
            , div [ classes ([ hide, ClassName "full-height" ] <> isActiveTab state WalletEmulator) ]
                [ slot _walletSlot unit Wallet.mkComponent unit (Just <<< HandleWalletMessage) ]
            , bottomPanel
            ]
        ]
    ]
  where
  bottomPanel = case state ^. _view of
    HaskellEditor -> HaskellEditor.bottomPanel state
    _ -> text mempty

  isActiveTab state' activeView = if state' ^. _view <<< to (eq activeView) then [ active ] else []
