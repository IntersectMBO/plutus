module MainFrame.State (component) where

import Prelude hiding (div)
import Auth (AuthRole(..), authStatusAuthRole, _GithubUser)
import BlocklyComponent.Types as Blockly
import BlocklyEditor.State as BlocklyEditor
import BlocklyEditor.Types (_marloweCode)
import BlocklyEditor.Types as BE
import BottomPanel.Types as BP
import ConfirmUnsavedNavigation.Types (Action(..)) as ConfirmUnsavedNavigation
import Control.Monad.Except (ExceptT(..), lift, runExcept, runExceptT)
import Control.Monad.Maybe.Extra (hoistMaybe)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Reader (class MonadAsk, asks, runReaderT)
import Control.Monad.State (modify_)
import Data.Bifunctor (lmap)
import Data.Either (Either(..), either, hush, note)
import Data.Foldable (fold, for_)
import Data.Lens (assign, has, preview, set, use, view, (^.))
import Data.Lens.Extra (peruse)
import Data.Lens.Index (ix)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (unwrap)
import Demos.Types (Action(..), Demo(..)) as Demos
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import Effect.Class.Console as Console
import Env (Env)
import Foreign.Generic (decodeJSON, encodeJSON)
import Gist (Gist, _GistId, gistDescription, gistId)
import Gists.Types (GistAction(..))
import Gists.Types (parseGistUrl) as Gists
import Halogen (Component, liftEffect, query, subscribe')
import Halogen as H
import Halogen.ActusBlockly as ActusBlockly
import Halogen.Analytics (withAnalytics)
import Halogen.Extra (mapSubmodule)
import Halogen.HTML (HTML)
import Halogen.Monaco (KeyBindings(DefaultBindings))
import Halogen.Monaco as Monaco
import Halogen.Query (HalogenM)
import Halogen.Query.EventSource (eventListenerEventSource)
import HaskellEditor.State as HaskellEditor
import HaskellEditor.Types (Action(..), State, _ContractString, _metadataHintInfo, initialState) as HE
import JavascriptEditor.State as JavascriptEditor
import JavascriptEditor.Types (Action(..), State, _ContractString, _metadataHintInfo, initialState) as JS
import JavascriptEditor.Types (CompilationState(..))
import Language.Haskell.Monaco as HM
import LoginPopup (openLoginPopup, informParentAndClose)
import MainFrame.Types (Action(..), ChildSlots, ModalView(..), Query(..), State, View(..), _actusBlocklySlot, _authStatus, _blocklyEditorState, _contractMetadata, _createGistResult, _gistId, _hasUnsavedChanges, _haskellState, _javascriptState, _jsEditorSlot, _loadGistResult, _marloweEditorState, _newProject, _projectName, _projects, _rename, _saveAs, _showBottomPanel, _showModal, _simulationState, _view, _walletSlot, _workflow, sessionToState, stateToSession)
import MainFrame.View (render)
import Marlowe (getApiGistsByGistId)
import Marlowe as Server
import Marlowe.ActusBlockly as AMB
import Marlowe.Extended.Metadata (emptyContractMetadata, getHintsFromMetadata)
import Marlowe.Gists (PlaygroundFiles, mkNewGist, playgroundFiles)
import MarloweEditor.State as MarloweEditor
import MarloweEditor.Types (_comesFromBlockly)
import MarloweEditor.Types as ME
import MetadataTab.State (carryMetadataAction)
import Network.RemoteData (RemoteData(..), _Success)
import Network.RemoteData as RemoteData
import NewProject.Types (Action(..), State, emptyState) as NewProject
import Prim.TypeError (class Warn, Text)
import Projects.State (handleAction) as Projects
import Projects.Types (Action(..), State, _projects, emptyState) as Projects
import Projects.Types (Lang(..))
import Rename.State (handleAction) as Rename
import Rename.Types (Action(..), State, _projectName, emptyState) as Rename
import Router (Route, SubRoute)
import Router as Router
import Routing.Duplex as RD
import Routing.Hash as Routing
import SaveAs.State (handleAction) as SaveAs
import SaveAs.Types (Action(..), State, _status, _projectName, emptyState) as SaveAs
import Servant.PureScript.Ajax (AjaxError, ErrorDescription(..), errorToString, runAjaxError)
import SessionStorage as SessionStorage
import SimulationPage.State as Simulation
import SimulationPage.Types as ST
import StaticData (gistIdLocalStorageKey)
import StaticData as StaticData
import Types (WebData)
import WalletSimulation.Types as Wallet
import Web.HTML (window) as Web
import Web.HTML.HTMLDocument (toEventTarget)
import Web.HTML.Window (document) as Web
import Web.HTML.Window as Window
import Web.UIEvent.KeyboardEvent as KE
import Web.UIEvent.KeyboardEvent.EventTypes (keyup)

initialState :: State
initialState =
  { view: HomePage
  , jsCompilationResult: NotCompiled
  , showBottomPanel: true
  , haskellState: HE.initialState
  , javascriptState: JS.initialState
  , marloweEditorState: ME.initialState
  , blocklyEditorState: BE.initialState
  , simulationState: ST.mkState
  , jsEditorKeybindings: DefaultBindings
  , activeJSDemo: mempty
  , contractMetadata: emptyContractMetadata
  , projects: Projects.emptyState
  , newProject: NewProject.emptyState
  , rename: Rename.emptyState
  , saveAs: SaveAs.emptyState
  , authStatus: NotAsked
  , gistId: Nothing
  , createGistResult: NotAsked
  , loadGistResult: Right NotAsked
  , projectName: "Untitled Project"
  , showModal: Nothing
  , hasUnsavedChanges: false
  , workflow: Nothing
  }

------------------------------------------------------------
component ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Component HTML Query Unit Void m
component =
  H.mkComponent
    { initialState: const initialState
    , render
    , eval:
        H.mkEval
          { handleQuery
          , handleAction: fullHandleAction
          , receive: const Nothing
          , initialize: Just Init
          , finalize: Nothing
          }
    }

toSimulation ::
  forall m a.
  Functor m =>
  HalogenM ST.State ST.Action ChildSlots Void m a -> HalogenM State Action ChildSlots Void m a
toSimulation = mapSubmodule _simulationState SimulationAction

toHaskellEditor ::
  forall m a.
  Functor m =>
  HalogenM HE.State HE.Action ChildSlots Void m a -> HalogenM State Action ChildSlots Void m a
toHaskellEditor = mapSubmodule _haskellState HaskellAction

toMarloweEditor ::
  forall m a.
  Functor m =>
  HalogenM ME.State ME.Action ChildSlots Void m a -> HalogenM State Action ChildSlots Void m a
toMarloweEditor = mapSubmodule _marloweEditorState MarloweEditorAction

toJavascriptEditor ::
  forall m a.
  Functor m =>
  HalogenM JS.State JS.Action ChildSlots Void m a -> HalogenM State Action ChildSlots Void m a
toJavascriptEditor = mapSubmodule _javascriptState JavascriptAction

toBlocklyEditor ::
  forall m a.
  Functor m =>
  HalogenM BE.State BE.Action ChildSlots Void m a -> HalogenM State Action ChildSlots Void m a
toBlocklyEditor = mapSubmodule _blocklyEditorState BlocklyEditorAction

toProjects ::
  forall m a.
  Functor m =>
  HalogenM Projects.State Projects.Action ChildSlots Void m a -> HalogenM State Action ChildSlots Void m a
toProjects = mapSubmodule _projects ProjectsAction

toNewProject ::
  forall m a.
  Functor m =>
  HalogenM NewProject.State NewProject.Action ChildSlots Void m a -> HalogenM State Action ChildSlots Void m a
toNewProject = mapSubmodule _newProject NewProjectAction

toDemos ::
  forall m a.
  Functor m =>
  HalogenM State Demos.Action ChildSlots Void m a -> HalogenM State Action ChildSlots Void m a
toDemos = mapSubmodule identity DemosAction

toRename ::
  forall m a.
  Functor m =>
  HalogenM Rename.State Rename.Action ChildSlots Void m a -> HalogenM State Action ChildSlots Void m a
toRename = mapSubmodule _rename RenameAction

toSaveAs ::
  forall m a.
  Functor m =>
  HalogenM SaveAs.State SaveAs.Action ChildSlots Void m a -> HalogenM State Action ChildSlots Void m a
toSaveAs = mapSubmodule _saveAs SaveAsAction

------------------------------------------------------------
handleSubRoute ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  SubRoute ->
  HalogenM State Action ChildSlots Void m Unit
handleSubRoute Router.Home = selectView HomePage

handleSubRoute Router.Simulation = selectView Simulation

handleSubRoute Router.MarloweEditor = selectView MarloweEditor

handleSubRoute Router.HaskellEditor = selectView HaskellEditor

handleSubRoute Router.JSEditor = selectView JSEditor

handleSubRoute Router.Blockly = selectView BlocklyEditor

handleSubRoute Router.ActusBlocklyEditor = selectView ActusBlocklyEditor

handleSubRoute Router.Wallets = selectView WalletEmulator

-- This route is supposed to be called by the github oauth flow after a succesful login flow
-- It is supposed to be run inside a popup window
handleSubRoute Router.GithubAuthCallback = do
  settings <- asks _.ajaxSettings
  authResult <- runAjax $ runReaderT Server.getApiOauthStatus settings
  case authResult of
    (Success authStatus) -> liftEffect $ informParentAndClose $ view authStatusAuthRole authStatus
    -- TODO: is it worth showing a particular view for Failure, NotAsked and Loading?
    -- Modifying this will mean to also modify the render function in the mainframe to be able to draw without
    -- the headers/footers as this is supposed to be a dialog/popup
    (Failure _) -> pure unit
    NotAsked -> pure unit
    Loading -> pure unit

handleRoute ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Route -> HalogenM State Action ChildSlots Void m Unit
handleRoute { gistId: (Just gistId), subroute } = do
  handleActionWithoutNavigationGuard (GistAction (SetGistUrl (unwrap gistId)))
  handleActionWithoutNavigationGuard (GistAction LoadGist)
  handleSubRoute subroute

handleRoute { subroute } = handleSubRoute subroute

handleQuery ::
  forall m a.
  MonadAff m =>
  MonadAsk Env m =>
  Query a ->
  HalogenM State Action ChildSlots Void m (Maybe a)
handleQuery (ChangeRoute route next) = do
  -- Without the following each route is handled twice, once when we call selectView ourselves
  -- and another which is triggered in Main, when the route changes.
  currentView <- use _view
  when (routeToView route /= Just currentView) $ handleRoute route
  pure $ Just next

------------------------------------------------------------
fullHandleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Action ->
  HalogenM State Action ChildSlots Void m Unit
fullHandleAction =
  withAccidentalNavigationGuard
    $ withSessionStorage
    $ withAnalytics
        handleAction

handleActionWithoutNavigationGuard ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleActionWithoutNavigationGuard =
  withSessionStorage
    $ withAnalytics
        ( handleAction
        )

-- This handleAction can be called recursively, but because we use HOF to extend the functionality
-- of the component, whenever we need to recurse we most likely be calling one of the extended functions
-- defined above (handleActionWithoutNavigationGuard or fullHandleAction)
handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction Init = do
  hash <- liftEffect Routing.getHash
  case (RD.parse Router.route) hash of
    Right route -> handleRoute route
    Left _ -> handleRoute { subroute: Router.Home, gistId: Nothing }
  document <- liftEffect $ Web.document =<< Web.window
  subscribe' \sid ->
    eventListenerEventSource keyup (toEventTarget document) (map (HandleKey sid) <<< KE.fromEvent)
  toSimulation $ Simulation.handleAction ST.Init
  toHaskellEditor $ HaskellEditor.handleAction HE.Init
  toMarloweEditor $ MarloweEditor.handleAction ME.Init
  toBlocklyEditor $ BlocklyEditor.handleAction BE.Init
  checkAuthStatus
  -- Load session data if available
  void
    $ runMaybeT do
        sessionJSON <- MaybeT $ liftEffect $ SessionStorage.getItem StaticData.sessionStorageKey
        session <- hoistMaybe $ hush $ runExcept $ decodeJSON sessionJSON
        let
          metadataHints = (getHintsFromMetadata (unwrap session).contractMetadata)
        H.modify_ $ sessionToState session
          <<< set (_haskellState <<< HE._metadataHintInfo) metadataHints
          <<< set (_javascriptState <<< JS._metadataHintInfo) (getHintsFromMetadata (unwrap session).contractMetadata)

handleAction (HandleKey sid ev)
  | KE.key ev == "Escape" = assign _showModal Nothing
  | KE.key ev == "Enter" = do
    modalView <- use _showModal
    case modalView of
      Just RenameProject -> handleAction (RenameAction Rename.SaveProject)
      Just SaveProjectAs -> handleAction (SaveAsAction SaveAs.SaveProject)
      _ -> pure unit
  | otherwise = pure unit

handleAction (HaskellAction action) = do
  toHaskellEditor (HaskellEditor.handleAction action)
  case action of
    HE.SendResultToSimulator -> do
      mContract <- peruse (_haskellState <<< HE._ContractString)
      let
        contract = fold mContract
      sendToSimulation contract
    HE.HandleEditorMessage (Monaco.TextChanged _) -> setUnsavedChangesForLanguage Haskell true
    HE.InitHaskellProject _ _ -> setUnsavedChangesForLanguage Haskell false
    HE.BottomPanelAction (BP.PanelAction (HE.MetadataAction metadataAction)) -> carryMetadataAction metadataAction
    _ -> pure unit

handleAction (JavascriptAction action) = do
  toJavascriptEditor (JavascriptEditor.handleAction action)
  case action of
    JS.SendResultToSimulator -> do
      mContract <- peruse (_javascriptState <<< JS._ContractString)
      let
        contract = fold mContract
      sendToSimulation contract
    JS.HandleEditorMessage (Monaco.TextChanged _) -> setUnsavedChangesForLanguage Javascript true
    JS.InitJavascriptProject _ _ -> setUnsavedChangesForLanguage Javascript false
    JS.BottomPanelAction (BP.PanelAction (JS.MetadataAction metadataAction)) -> carryMetadataAction metadataAction
    _ -> pure unit

handleAction (MarloweEditorAction action) = do
  toMarloweEditor (MarloweEditor.handleAction action)
  case action of
    ME.SendToSimulator -> do
      mContents <- MarloweEditor.editorGetValue
      for_ mContents \contents ->
        sendToSimulation contents
    ME.ViewAsBlockly -> do
      comesFromBlockly <- use (_marloweEditorState <<< _comesFromBlockly)
      mSource <- MarloweEditor.editorGetValue
      for_ mSource \source -> do
        void $ toBlocklyEditor $ BlocklyEditor.handleAction (BE.InitBlocklyProject (not comesFromBlockly) source)
        assign _workflow (Just Blockly)
        selectView BlocklyEditor
    ME.HandleEditorMessage (Monaco.TextChanged _) -> setUnsavedChangesForLanguage Marlowe true
    ME.InitMarloweProject _ -> setUnsavedChangesForLanguage Marlowe false
    ME.BottomPanelAction (BP.PanelAction (ME.MetadataAction metadataAction)) -> carryMetadataAction metadataAction
    _ -> pure unit

handleAction (BlocklyEditorAction action) = do
  toBlocklyEditor $ BlocklyEditor.handleAction action
  case action of
    BE.SendToSimulator -> do
      mCode <- use (_blocklyEditorState <<< _marloweCode)
      for_ mCode \contents -> sendToSimulation contents
    BE.ViewAsMarlowe -> do
      -- TODO: doing an effect that returns a maybe value and doing an action on the possible
      -- result is a pattern that we have repeated a lot in this file. See if we could refactor
      -- into something like this: https://github.com/input-output-hk/plutus/pull/2560#discussion_r549892291
      mCode <- use (_blocklyEditorState <<< _marloweCode)
      for_ mCode \code -> do
        selectView MarloweEditor
        assign _workflow (Just Marlowe)
        toMarloweEditor $ MarloweEditor.handleAction $ ME.InitMarloweProject code
      assign (_marloweEditorState <<< _comesFromBlockly) true
    BE.HandleBlocklyMessage Blockly.CodeChange -> setUnsavedChangesForLanguage Blockly true
    BE.BottomPanelAction (BP.PanelAction (BE.MetadataAction metadataAction)) -> carryMetadataAction metadataAction
    _ -> pure unit

handleAction (SimulationAction action) = do
  toSimulation (Simulation.handleAction action)
  case action of
    ST.EditSource -> do
      mLang <- use _workflow
      for_ mLang \lang -> selectView $ selectLanguageView lang
    _ -> pure unit

handleAction (HandleWalletMessage Wallet.SendContractToWallet) = do
  mContract <- toSimulation $ Simulation.getCurrentContract
  case mContract of
    Nothing -> liftEffect $ Console.warn "Could not import contract from simulator"
    Just contract -> void $ query _walletSlot unit (Wallet.LoadContract contract unit)

handleAction (ChangeView view) = selectView view

handleAction (ShowBottomPanel val) = do
  assign _showBottomPanel val
  pure unit

handleAction (HandleActusBlocklyMessage ActusBlockly.Initialized) = pure unit

handleAction (HandleActusBlocklyMessage (ActusBlockly.CurrentTerms flavour terms)) = do
  let
    parsedTermsEither = AMB.parseActusJsonCode terms
  settings <- asks _.ajaxSettings
  case parsedTermsEither of
    Left e -> void $ query _actusBlocklySlot unit (ActusBlockly.SetError ("Couldn't parse contract-terms - " <> (show e)) unit)
    Right parsedTerms -> do
      result <- case flavour of
        ActusBlockly.FS -> runAjax $ flip runReaderT settings $ (Server.postApiActusGenerate parsedTerms)
        ActusBlockly.F -> runAjax $ flip runReaderT settings $ (Server.postApiActusGeneratestatic parsedTerms)
      case result of
        Success contractAST -> sendToSimulation contractAST
        Failure e -> void $ query _actusBlocklySlot unit (ActusBlockly.SetError ("Server error! " <> (showErrorDescription (runAjaxError e).description)) unit)
        _ -> void $ query _actusBlocklySlot unit (ActusBlockly.SetError "Unknown server error!" unit)

handleAction (HandleActusBlocklyMessage ActusBlockly.CodeChange) = setUnsavedChangesForLanguage Actus true

-- TODO: modify gist action type to take a gistid as a parameter
-- https://github.com/input-output-hk/plutus/pull/2498/files#r533478042
handleAction (ProjectsAction action@(Projects.LoadProject lang gistId)) = do
  assign _createGistResult Loading
  res <-
    runExceptT
      $ do
          settings <- asks _.ajaxSettings
          gist <- flip runReaderT settings $ getApiGistsByGistId gistId
          lift $ loadGist gist
          pure gist
  case res of
    Right gist ->
      modify_
        ( set _createGistResult (Success gist)
            <<< set _showModal Nothing
            <<< set _workflow (Just lang)
        )
    Left error ->
      modify_
        ( set _createGistResult (Failure error)
            <<< set (_projects <<< Projects._projects) (Failure "Failed to load gist")
            <<< set _workflow Nothing
        )
  toProjects $ Projects.handleAction action
  selectView $ selectLanguageView lang

handleAction (ProjectsAction Projects.Cancel) = fullHandleAction CloseModal

handleAction (ProjectsAction action) = toProjects $ Projects.handleAction action

handleAction (NewProjectAction (NewProject.CreateProject lang)) = do
  modify_
    ( set _projectName "New Project"
        <<< set _gistId Nothing
        <<< set _createGistResult NotAsked
        <<< set _contractMetadata emptyContractMetadata
    )
  liftEffect $ SessionStorage.setItem gistIdLocalStorageKey mempty
  -- We reset all editors and then initialize the selected language.
  toHaskellEditor $ HaskellEditor.handleAction $ HE.InitHaskellProject mempty mempty
  toJavascriptEditor $ JavascriptEditor.handleAction $ JS.InitJavascriptProject mempty mempty
  toMarloweEditor $ MarloweEditor.handleAction $ ME.InitMarloweProject mempty
  toBlocklyEditor $ BlocklyEditor.handleAction $ BE.InitBlocklyProject true mempty
  -- TODO: implement ActusBlockly.SetCode
  case lang of
    Haskell ->
      for_ (Map.lookup "Example" StaticData.demoFiles) \contents -> do
        toHaskellEditor $ HaskellEditor.handleAction $ HE.InitHaskellProject mempty contents
    Javascript ->
      for_ (Map.lookup "Example" StaticData.demoFilesJS) \contents -> do
        toJavascriptEditor $ JavascriptEditor.handleAction $ JS.InitJavascriptProject mempty contents
    Marlowe ->
      for_ (Map.lookup "Example" StaticData.marloweContracts) \contents -> do
        toMarloweEditor $ MarloweEditor.handleAction $ ME.InitMarloweProject contents
    Blockly ->
      for_ (Map.lookup "Example" StaticData.marloweContracts) \contents -> do
        toBlocklyEditor $ BlocklyEditor.handleAction $ BE.InitBlocklyProject true contents
    _ -> pure unit
  selectView $ selectLanguageView lang
  modify_
    ( set _showModal Nothing
        <<< set _workflow (Just lang)
        <<< set _hasUnsavedChanges false
    )

handleAction (NewProjectAction NewProject.Cancel) = fullHandleAction CloseModal

handleAction (DemosAction action@(Demos.LoadDemo lang (Demos.Demo key))) = do
  case lang of
    Haskell ->
      for_ (Map.lookup key StaticData.demoFiles) \contents ->
        toHaskellEditor $ HaskellEditor.handleAction $ HE.InitHaskellProject metadataHints contents
    Javascript ->
      for_ (Map.lookup key StaticData.demoFilesJS) \contents -> do
        toJavascriptEditor $ JavascriptEditor.handleAction $ JS.InitJavascriptProject metadataHints contents
    Marlowe -> do
      for_ (preview (ix key) StaticData.marloweContracts) \contents -> do
        toMarloweEditor $ MarloweEditor.handleAction $ ME.InitMarloweProject contents
    Blockly -> do
      for_ (preview (ix key) StaticData.marloweContracts) \contents -> do
        toBlocklyEditor $ BlocklyEditor.handleAction $ BE.InitBlocklyProject true contents
    Actus -> pure unit
  modify_
    ( set _showModal Nothing
        <<< set _workflow (Just lang)
        <<< set _hasUnsavedChanges false
        <<< set _gistId Nothing
        <<< set _projectName metadata.contractName
        <<< set _contractMetadata metadata
    )
  selectView $ selectLanguageView lang
  where
  metadata = fromMaybe emptyContractMetadata $ Map.lookup key StaticData.demoFilesMetadata

  metadataHints = getHintsFromMetadata metadata

handleAction (DemosAction Demos.Cancel) = fullHandleAction CloseModal

handleAction (RenameAction action@Rename.SaveProject) = do
  projectName <- use (_rename <<< Rename._projectName)
  modify_
    ( set _projectName projectName
        <<< set _showModal Nothing
    )
  toRename $ Rename.handleAction action

handleAction (RenameAction action) = toRename $ Rename.handleAction action

handleAction (SaveAsAction action@SaveAs.SaveProject) = do
  currentName <- use _projectName
  currentGistId <- use _gistId
  projectName <- use (_saveAs <<< SaveAs._projectName)
  modify_
    ( set _gistId Nothing
        <<< set _projectName projectName
        <<< set (_saveAs <<< SaveAs._status) Loading
    )
  handleGistAction PublishOrUpdateGist
  res <- peruse (_createGistResult <<< _Success)
  case res of
    Just gist -> do
      liftEffect $ SessionStorage.setItem gistIdLocalStorageKey (gist ^. (gistId <<< _GistId))
      modify_
        ( set _showModal Nothing
            <<< set (_saveAs <<< SaveAs._status) NotAsked
        )
    Nothing ->
      modify_
        ( set (_saveAs <<< SaveAs._status) (Failure "Could not save project")
            <<< set _projectName currentName
            <<< set _gistId currentGistId
        )
  toSaveAs $ SaveAs.handleAction action

handleAction (SaveAsAction SaveAs.Cancel) = fullHandleAction CloseModal

handleAction (SaveAsAction action) = toSaveAs $ SaveAs.handleAction action

handleAction CheckAuthStatus = checkAuthStatus

handleAction (GistAction subEvent) = handleGistAction subEvent

handleAction (OpenModal OpenProject) = do
  assign _showModal $ Just OpenProject
  toProjects $ Projects.handleAction Projects.LoadProjects

handleAction (OpenModal RenameProject) = do
  currentName <- use _projectName
  assign (_rename <<< Rename._projectName) currentName
  assign _showModal $ Just RenameProject

handleAction (OpenModal modalView) = assign _showModal $ Just modalView

handleAction CloseModal = assign _showModal Nothing

handleAction (ChangeProjectName name) = assign _projectName name

handleAction (OpenLoginPopup intendedAction) = do
  authRole <- liftAff openLoginPopup
  fullHandleAction CloseModal
  assign (_authStatus <<< _Success <<< authStatusAuthRole) authRole
  case authRole of
    Anonymous -> pure unit
    GithubUser -> fullHandleAction intendedAction

handleAction (ConfirmUnsavedNavigationAction intendedAction modalAction) = handleConfirmUnsavedNavigationAction intendedAction modalAction

sendToSimulation ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  String ->
  HalogenM State Action ChildSlots Void m Unit
sendToSimulation contract = do
  selectView Simulation
  toSimulation $ Simulation.handleAction (ST.LoadContract contract)

selectLanguageView :: Lang -> View
selectLanguageView = case _ of
  Haskell -> HaskellEditor
  Marlowe -> MarloweEditor
  Blockly -> BlocklyEditor
  Javascript -> JSEditor
  Actus -> ActusBlocklyEditor

routeToView :: Route -> Maybe View
routeToView { subroute } = case subroute of
  Router.Home -> Just HomePage
  Router.Simulation -> Just Simulation
  Router.HaskellEditor -> Just HaskellEditor
  Router.MarloweEditor -> Just MarloweEditor
  Router.JSEditor -> Just JSEditor
  Router.ActusBlocklyEditor -> Just ActusBlocklyEditor
  Router.Blockly -> Just BlocklyEditor
  Router.Wallets -> Just WalletEmulator
  Router.GithubAuthCallback -> Nothing

viewToRoute :: View -> Router.SubRoute
viewToRoute = case _ of
  HomePage -> Router.Home
  MarloweEditor -> Router.MarloweEditor
  Simulation -> Router.Simulation
  HaskellEditor -> Router.HaskellEditor
  JSEditor -> Router.JSEditor
  BlocklyEditor -> Router.Blockly
  WalletEmulator -> Router.Wallets
  ActusBlocklyEditor -> Router.ActusBlocklyEditor

------------------------------------------------------------
showErrorDescription :: ErrorDescription -> String
showErrorDescription (DecodingError err@"(\"Unexpected token E in JSON at position 0\" : Nil)") = "BadResponse"

showErrorDescription (DecodingError err) = "DecodingError: " <> err

showErrorDescription NotFound = "NotFound"

showErrorDescription (ResponseError status body) = "ResponseError: " <> show status <> " " <> body

showErrorDescription (ResponseFormatError err) = "ResponseFormatError: " <> err

showErrorDescription (ConnectionError err) = "ConnectionError: " <> err

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM State Action ChildSlots Void m) a ->
  HalogenM State Action ChildSlots Void m (WebData a)
runAjax action = RemoteData.fromEither <$> runExceptT action

------------------------------------------------------------
checkAuthStatus ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  HalogenM State Action ChildSlots Void m Unit
checkAuthStatus = do
  settings <- asks _.ajaxSettings
  assign _authStatus Loading
  authResult <- runAjax $ runReaderT Server.getApiOauthStatus settings
  assign _authStatus authResult

------------------------------------------------------------
createFiles ::
  forall m.
  MonadAff m =>
  MonadAsk Env m => HalogenM State Action ChildSlots Void m PlaygroundFiles
createFiles = do
  let
    pruneEmpty :: forall a. Eq a => Monoid a => Maybe a -> Maybe a
    pruneEmpty (Just v)
      | v == mempty = Nothing

    pruneEmpty m = m

    -- playground is a meta-data file that we currently just use as a tag to check if a gist is a marlowe playground gist
    playground = "{}"
  metadata <- Just <$> encodeJSON <$> use _contractMetadata
  workflow <- use _workflow
  let
    emptyFiles = (mempty :: PlaygroundFiles) { playground = playground, metadata = metadata }
  case workflow of
    Just Marlowe -> do
      marlowe <- pruneEmpty <$> MarloweEditor.editorGetValue
      pure $ emptyFiles { marlowe = marlowe }
    Just Blockly -> do
      blockly <- pruneEmpty <$> BlocklyEditor.editorGetValue
      pure $ emptyFiles { blockly = blockly }
    Just Haskell -> do
      haskell <- pruneEmpty <$> HaskellEditor.editorGetValue
      pure $ emptyFiles { haskell = haskell }
    Just Javascript -> do
      javascript <- pruneEmpty <$> toJavascriptEditor JavascriptEditor.editorGetValue
      pure $ emptyFiles { javascript = javascript }
    Just Actus -> do
      actus <- pruneEmpty <$> query _actusBlocklySlot unit (H.request ActusBlockly.GetWorkspace)
      pure $ emptyFiles { actus = actus }
    Nothing -> mempty

handleGistAction ::
  forall m.
  Warn (Text "Check if the handler for LoadGist is being used") =>
  Warn (Text "SCP-1591 Saving failure does not provide enough information") =>
  MonadAff m =>
  MonadAsk Env m =>
  GistAction -> HalogenM State Action ChildSlots Void m Unit
handleGistAction PublishOrUpdateGist = do
  description <- use _projectName
  files <- createFiles
  let
    newGist = mkNewGist description $ files
  void
    $ runMaybeT do
        mGist <- use _gistId
        assign _createGistResult Loading
        settings <- asks _.ajaxSettings
        newResult <-
          lift
            $ case mGist of
                Nothing -> runAjax $ flip runReaderT settings $ Server.postApiGists newGist
                Just gistId -> runAjax $ flip runReaderT settings $ Server.postApiGistsByGistId newGist gistId
        assign _createGistResult newResult
        gistId <- hoistMaybe $ preview (_Success <<< gistId) newResult
        modify_
          ( set _gistId (Just gistId)
              <<< set _loadGistResult (Right NotAsked)
              <<< set _hasUnsavedChanges false
          )

handleGistAction (SetGistUrl url) = do
  case Gists.parseGistUrl url of
    Right newGistUrl ->
      modify_
        ( set _createGistResult NotAsked
            <<< set _loadGistResult (Right NotAsked)
            <<< set _gistId (Just newGistUrl)
        )
    Left _ -> pure unit

-- TODO: I think this action is not being called.
-- > The issue is that for historical reasons, the gist actions rely on gist id stored in the state,
-- > so we need to set the appropriate state before handling the gist action. This should probably be
-- > changed to have gist action type taking gist id as a parameter.
-- https://github.com/input-output-hk/plutus/pull/2498#discussion_r533478042
handleGistAction LoadGist = do
  res <-
    runExceptT
      $ do
          settings <- asks _.ajaxSettings
          eGistId <- ExceptT $ note "Gist Id not set." <$> use _gistId
          assign _loadGistResult $ Right Loading
          aGist <- lift $ runAjax $ flip runReaderT settings $ Server.getApiGistsByGistId eGistId
          assign _loadGistResult $ Right aGist
          gist <- ExceptT $ pure $ toEither (Left "Gist not loaded.") $ lmap errorToString aGist
          lift $ loadGist gist
          pure aGist
  assign _loadGistResult res
  where
  toEither :: forall e a. Either e a -> RemoteData e a -> Either e a
  toEither _ (Success a) = Right a

  toEither _ (Failure e) = Left e

  toEither x Loading = x

  toEither x NotAsked = x

-- other gist actions are irrelevant here
handleGistAction _ = pure unit

loadGist ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Gist ->
  HalogenM State Action ChildSlots Void m Unit
loadGist gist = do
  let
    { marlowe
    , blockly
    , haskell
    , javascript
    , actus
    , metadata: mMetadataJSON
    } = playgroundFiles gist

    description = view gistDescription gist

    gistId' = preview gistId gist

    metadata = maybe emptyContractMetadata (either (const emptyContractMetadata) identity <<< runExcept <<< decodeJSON) mMetadataJSON

    metadataHints = getHintsFromMetadata metadata
  -- Restore or reset all editors
  toHaskellEditor $ HaskellEditor.handleAction $ HE.InitHaskellProject metadataHints $ fromMaybe mempty haskell
  toJavascriptEditor $ JavascriptEditor.handleAction $ JS.InitJavascriptProject metadataHints $ fromMaybe mempty javascript
  toMarloweEditor $ MarloweEditor.handleAction $ ME.InitMarloweProject $ fromMaybe mempty marlowe
  toBlocklyEditor $ BlocklyEditor.handleAction $ BE.InitBlocklyProject true $ fromMaybe mempty blockly
  assign _contractMetadata metadata
  -- Actus doesn't have a SetCode to reset for the moment, so we only set if present.
  -- TODO add SetCode to Actus
  for_ actus \xml -> query _actusBlocklySlot unit (ActusBlockly.LoadWorkspace xml unit)
  modify_
    ( set _gistId gistId'
        <<< set _projectName description
    )

------------------------------------------------------------
-- Handles the actions fired by the Confirm Unsaved Navigation modal
handleConfirmUnsavedNavigationAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Action ->
  ConfirmUnsavedNavigation.Action ->
  HalogenM State Action ChildSlots Void m Unit
handleConfirmUnsavedNavigationAction intendedAction modalAction = do
  fullHandleAction CloseModal
  case modalAction of
    ConfirmUnsavedNavigation.Cancel -> pure unit
    ConfirmUnsavedNavigation.DontSaveProject -> handleActionWithoutNavigationGuard intendedAction
    ConfirmUnsavedNavigation.SaveProject -> do
      state <- H.get
      -- TODO: This was taken from the view, from the gistModal helper. I think we should
      -- refactor into a `Save (Maybe Action)` action. The handler for that should do
      -- this check and call the next action as a continuation
      if has (_authStatus <<< _Success <<< authStatusAuthRole <<< _GithubUser) state then do
        fullHandleAction $ GistAction PublishOrUpdateGist
        fullHandleAction intendedAction
      else
        fullHandleAction $ OpenModal $ GithubLogin $ ConfirmUnsavedNavigationAction intendedAction modalAction

setUnsavedChangesForLanguage :: forall m. Lang -> Boolean -> HalogenM State Action ChildSlots Void m Unit
setUnsavedChangesForLanguage lang value = do
  workflow <- use _workflow
  when (workflow == Just lang)
    $ assign _hasUnsavedChanges value

-- This is a HOF intented to be used on top of handleAction. It prevents the user from accidentally doing an Action that
-- would result in losing the progress.
withAccidentalNavigationGuard ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  (Action -> HalogenM State Action ChildSlots Void m Unit) ->
  Action ->
  HalogenM State Action ChildSlots Void m Unit
withAccidentalNavigationGuard handleAction' action = do
  currentView <- use _view
  hasUnsavedChanges <- use _hasUnsavedChanges
  if viewIsGuarded currentView && actionIsGuarded && hasUnsavedChanges then
    -- If the action would result in the user losing the work, we present a
    -- modal to confirm, cancel or save the work and we preserve the intended action
    -- to be executed after.
    fullHandleAction $ OpenModal $ ConfirmUnsavedNavigation action
  else
    handleAction' action
  where
  -- Which pages needs to be guarded.
  viewIsGuarded = case _ of
    HomePage -> false
    _ -> true

  -- What actions would result in losing the work.
  actionIsGuarded = case action of
    (ChangeView HomePage) -> true
    (ChangeView ActusBlocklyEditor) -> true
    (NewProjectAction (NewProject.CreateProject _)) -> true
    (ProjectsAction (Projects.LoadProject _ _)) -> true
    (DemosAction (Demos.LoadDemo _ _)) -> true
    _ -> false

------------------------------------------------------------
selectView ::
  forall m action message.
  MonadEffect m =>
  View -> HalogenM State action ChildSlots message m Unit
selectView view = do
  liftEffect $ Routing.setHash (RD.print Router.route { subroute: viewToRoute view, gistId: Nothing })
  assign _view view
  liftEffect do
    window <- Web.window
    Window.scroll 0 0 window
  case view of
    HomePage -> modify_ (set _workflow Nothing <<< set _hasUnsavedChanges false)
    Simulation -> do
      Simulation.editorSetTheme
    MarloweEditor -> do
      MarloweEditor.editorSetTheme
    HaskellEditor -> do
      HaskellEditor.editorSetTheme
    JSEditor -> do
      void $ query _jsEditorSlot unit (Monaco.SetTheme HM.daylightTheme.name unit)
    BlocklyEditor -> pure unit
    WalletEmulator -> pure unit
    ActusBlocklyEditor -> do
      void $ query _actusBlocklySlot unit (ActusBlockly.Resize unit)

------------------------------------------------------------
withSessionStorage ::
  forall m.
  MonadAff m =>
  (Action -> HalogenM State Action ChildSlots Void m Unit) ->
  Action ->
  HalogenM State Action ChildSlots Void m Unit
withSessionStorage handleAction' action = do
  preSession <- H.gets stateToSession
  handleAction' action
  postSession <- H.gets stateToSession
  when (preSession /= postSession)
    $ liftEffect
    $ SessionStorage.setItem StaticData.sessionStorageKey
    $ encodeJSON postSession
