module MainFrame.State (mkMainFrame) where

import Auth (AuthRole(..), authStatusAuthRole, _GithubUser)
import ConfirmUnsavedNavigation.State (handleAction) as ConfirmUnsavedNavigation
import ConfirmUnsavedNavigation.Types (Action(..), State, emptyState) as ConfirmUnsavedNavigation
import ConfirmUnsavedNavigation.Types (_wantsToSaveProject)
import Control.Monad.Except (ExceptT(..), lift, runExceptT)
import Control.Monad.Maybe.Extra (hoistMaybe)
import Control.Monad.Maybe.Trans (runMaybeT)
import Control.Monad.Reader (runReaderT)
import ConfirmUnsavedNavigation.Types (Action(..), State) as ConfirmUnsavedNavigation
import Control.Monad.State (modify_)
import Data.Bifunctor (lmap)
import Data.Either (Either(..), note)
import Data.Foldable (fold, for_)
import Data.Lens (assign, preview, use, view, set, (^.), has)
import Data.Lens.Extra (peruse)
import Data.Lens.Index (ix)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Debug.Trace (spy)
import Demos.Types (Action(..), Demo(..)) as Demos
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import Effect.Console as Console
import Examples.Haskell.Contracts (example) as HE
import Examples.JS.Contracts (example) as JE
import Gist (Gist, _GistId, gistDescription, gistId)
import Gists.Types (GistAction(..))
import Gists.Types (parseGistUrl) as Gists
import Halogen (Component, liftEffect, query, subscribe')
import Halogen as H
import Halogen.ActusBlockly as ActusBlockly
import Halogen.Analytics (handleActionWithAnalyticsTracking)
import Halogen.Blockly (Message(..))
import Halogen.Blockly as Blockly
import Halogen.Extra (mapSubmodule)
import Halogen.HTML (HTML)
import Halogen.Monaco (KeyBindings(DefaultBindings))
import Halogen.Monaco as Monaco
import Halogen.Query (HalogenM)
import Halogen.Query.EventSource (eventListenerEventSource)
import HaskellEditor.State (editorGetValue, editorResize, editorSetValue, handleAction) as HaskellEditor
import HaskellEditor.Types (Action(..), State, _ContractString, initialState) as HE
import JavascriptEditor.State as JavascriptEditor
import JavascriptEditor.Types (Action(..), State, _ContractString, initialState) as JS
import JavascriptEditor.Types (CompilationState(..))
import Language.Haskell.Monaco as HM
import LocalStorage as LocalStorage
import LoginPopup (openLoginPopup, informParentAndClose)
import MainFrame.Types (Action(..), ChildSlots, ModalView(..), Query(..), State(State), View(..), _actusBlocklySlot, _authStatus, _blocklySlot, _confirmUnsavedNavigation, _createGistResult, _gistId, _hasUnsavedChanges, _haskellEditorSlot, _haskellState, _javascriptState, _jsEditorSlot, _loadGistResult, _newProject, _projectName, _projects, _rename, _saveAs, _showBottomPanel, _showModal, _simulationState, _view, _walletSlot)
import MainFrame.View (render)
import Marlowe (SPParams_, getApiGistsByGistId)
import Marlowe as Server
import Marlowe.ActusBlockly as AMB
import Marlowe.Gists (mkNewGist, playgroundFiles)
import Network.RemoteData (RemoteData(..), _Success)
import Network.RemoteData as RemoteData
import NewProject.State (handleAction) as NewProject
import NewProject.Types (Action(..), State, emptyState) as NewProject
import Prelude (class Eq, class Functor, class Monoid, Unit, Void, bind, const, discard, flip, identity, map, mempty, otherwise, pure, show, unit, void, ($), (<$>), (<<<), (<>), (=<<), (==))
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
import SaveAs.Types (Action(..), State, _error, _projectName, emptyState) as SaveAs
import Servant.PureScript.Ajax (AjaxError, ErrorDescription(..), errorToString, runAjaxError)
import Servant.PureScript.Settings (SPSettings_)
import Simulation as Simulation
import Simulation.Types (_source)
import Simulation.Types as ST
import StaticData (bufferLocalStorageKey, gistIdLocalStorageKey, jsBufferLocalStorageKey, marloweBufferLocalStorageKey)
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
  State
    { view: Simulation {- TODO: I think we should change the type to Maybe and the initial state should be Nothing-}
    , jsCompilationResult: NotCompiled
    , blocklyState: Nothing
    , actusBlocklyState: Nothing
    , showBottomPanel: true
    , haskellState: HE.initialState
    , javascriptState: JS.initialState
    , simulationState: ST.mkState
    , jsEditorKeybindings: DefaultBindings
    , activeJSDemo: mempty
    , projects: Projects.emptyState
    , newProject: NewProject.emptyState
    , rename: Rename.emptyState
    , saveAs: SaveAs.emptyState
    , confirmUnsavedNavigation: ConfirmUnsavedNavigation.emptyState
    , authStatus: NotAsked
    , gistId: Nothing
    , createGistResult: NotAsked
    , loadGistResult: Right NotAsked
    , projectName: "Untitled Project"
    , showModal: Nothing
    , hasUnsavedChanges: false
    }

------------------------------------------------------------
mkMainFrame ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ -> Component HTML Query Unit Void m
mkMainFrame settings =
  H.mkComponent
    { initialState: const initialState
    , render: render settings
    , eval:
        H.mkEval
          { handleQuery: handleQuery settings
          -- FIXME try to add a handleActionWithPreventAccidentalNavigation
          -- to avoid having to persist the boolean
          , handleAction: handleActionWithAnalyticsTracking (handleAction settings)
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

toJavascriptEditor ::
  forall m a.
  Functor m =>
  HalogenM JS.State JS.Action ChildSlots Void m a -> HalogenM State Action ChildSlots Void m a
toJavascriptEditor = mapSubmodule _javascriptState JavascriptAction

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

toConfirmUnsavedNavigation ::
  forall m a.
  Functor m =>
  Action ->
  HalogenM ConfirmUnsavedNavigation.State ConfirmUnsavedNavigation.Action ChildSlots Void m a -> HalogenM State Action ChildSlots Void m a
toConfirmUnsavedNavigation intendedAction = mapSubmodule _confirmUnsavedNavigation (ConfirmUnsavedNavigationAction intendedAction)

handleSubRoute ::
  forall m.
  MonadEffect m =>
  MonadAff m =>
  SPSettings_ SPParams_ ->
  SubRoute -> HalogenM State Action ChildSlots Void m Unit
handleSubRoute settings Router.Home = selectView HomePage

handleSubRoute settings Router.Simulation = selectView Simulation

handleSubRoute settings Router.HaskellEditor = selectView HaskellEditor

handleSubRoute settings Router.JSEditor = selectView JSEditor

handleSubRoute settings Router.Blockly = selectView BlocklyEditor

handleSubRoute settings Router.ActusBlocklyEditor = selectView ActusBlocklyEditor

handleSubRoute settings Router.Wallets = selectView WalletEmulator

-- This route is supposed to be called by the github oauth flow after a succesful login flow
-- It is supposed to be run inside a popup window
handleSubRoute settings Router.GithubAuthCallback = do
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
  SPSettings_ SPParams_ ->
  Route -> HalogenM State Action ChildSlots Void m Unit
handleRoute settings { gistId: (Just gistId), subroute } = do
  handleAction settings (GistAction (SetGistUrl (unwrap gistId)))
  handleAction settings (GistAction LoadGist)
  handleSubRoute settings subroute

handleRoute settings { subroute } = handleSubRoute settings subroute

handleQuery ::
  forall m a.
  Functor m =>
  MonadEffect m =>
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Query a ->
  HalogenM State Action ChildSlots Void m (Maybe a)
handleQuery settings (ChangeRoute route next) = do
  -- Without the following each route is handled twice, once when we call selectView ourselves
  -- and another which is triggered in Main, when the route changes.
  currentView <- use _view
  when (routeToView route /= Just currentView) $ handleRoute settings route
  pure $ Just next

-- FIXME: Delete before merging
-- showHandleAction ::
--   forall m.
--   MonadAff m =>
--   SPSettings_ SPParams_ ->
--   Action ->
--   HalogenM State Action ChildSlots Void m Unit
-- showHandleAction settings action = handleAction settings $ spy "MainFrame.handleAction" action
-- TODO: Should we refactor the settings so that it's a ReaderT or part of the State?
handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction settings Init = do
  hash <- liftEffect Routing.getHash
  case (RD.parse Router.route) hash of
    Right route -> handleRoute settings route
    Left _ -> handleRoute settings { subroute: Router.Home, gistId: Nothing }
  document <- liftEffect $ Web.document =<< Web.window
  subscribe' \sid ->
    eventListenerEventSource keyup (toEventTarget document) (map (HandleKey sid) <<< KE.fromEvent)
  toSimulation $ Simulation.handleAction settings ST.Init
  checkAuthStatus settings

handleAction settings (HandleKey sid ev)
  | KE.key ev == "Escape" = assign _showModal Nothing
  | KE.key ev == "Enter" = do
    modalView <- use _showModal
    case modalView of
      Just RenameProject -> handleAction settings (RenameAction Rename.SaveProject)
      Just SaveProjectAs -> handleAction settings (SaveAsAction SaveAs.SaveProject)
      _ -> pure unit
  | otherwise = pure unit

handleAction s (HaskellAction action) = do
  toHaskellEditor (HaskellEditor.handleAction s action)
  case action of
    HE.SendResultToSimulator -> do
      mContract <- peruse (_haskellState <<< HE._ContractString)
      let
        contract = fold mContract
      sendToSimulation s Haskell contract
    HE.SendResultToBlockly -> do
      assign (_simulationState <<< _source) Haskell
      selectView BlocklyEditor
    (HE.HandleEditorMessage ev) -> do
      -- FIXME: remove
      void $ pure $ spy "MainFrame.handleAction: Haskell editor message" ev
      assign _hasUnsavedChanges true
    _ -> pure unit

handleAction s (JavascriptAction action) = do
  toJavascriptEditor (JavascriptEditor.handleAction s action)
  case action of
    JS.SendResultToSimulator -> do
      mContract <- peruse (_javascriptState <<< JS._ContractString)
      let
        contract = fold mContract
      sendToSimulation s Javascript contract
    JS.SendResultToBlockly -> do
      assign (_simulationState <<< _source) Javascript
      selectView BlocklyEditor
    (JS.HandleEditorMessage ev) -> do
      -- FIXME: right now creating a JS project is always set as Unsaved because we have multiple events
      -- after the actual creation
      void $ pure $ spy "MainFrame.handleAction: Javascript editor message" ev
      assign _hasUnsavedChanges true
    _ -> pure unit

handleAction settings (SimulationAction action) = do
  toSimulation (Simulation.handleAction settings action)
  case action of
    ST.SetBlocklyCode -> do
      mSource <- Simulation.editorGetValue
      for_ mSource \source -> void $ query _blocklySlot unit (Blockly.SetCode source unit)
      selectView BlocklyEditor
    ST.EditHaskell -> selectView HaskellEditor
    ST.EditJavascript -> selectView JSEditor
    ST.EditActus -> selectView ActusBlocklyEditor
    (ST.HandleEditorMessage ev) -> do
      -- FIXME: right now creating a Marlowe project is always set as Unsaved because we have multiple events
      -- after the actual creation
      void $ pure $ spy "MainFrame.handleAction: Marlowe editor message" ev
      assign _hasUnsavedChanges true
    _ -> pure unit

handleAction _ SendBlocklyToSimulator = void $ query _blocklySlot unit (Blockly.GetCodeQuery unit)

handleAction _ (HandleWalletMessage Wallet.SendContractToWallet) = do
  contract <- toSimulation $ Simulation.getCurrentContract
  void $ query _walletSlot unit (Wallet.LoadContract contract unit)

handleAction settings (ChangeView ActusBlocklyEditor) = do
  -- FIXME check if this really really needs to be called as a pre-action, if not, unify it
  -- with the selectView `case view`
  assign (_simulationState <<< ST._source) Actus
  selectView ActusBlocklyEditor

handleAction settings action@(ChangeView view) =
  preventAccidentalNavigation settings action do
    selectView view

handleAction _ (ShowBottomPanel val) = do
  assign _showBottomPanel val
  pure unit

handleAction settings (HandleBlocklyMessage (CurrentCode code)) = do
  -- TODO: We used to block moving code to the simulation however due to the new UX there is no way to navigate this
  -- I am leaving the old code here as we want to come up with a solution asap and it will involve using this same logic
  -- The same occurs with Actus too
  -- hasStarted <- use (_simulationState <<< _marloweState <<< to (\states -> (NEL.length states) > 1))
  -- if hasStarted then
  --   void $ query _blocklySlot unit (Blockly.SetError "You can't send new code to a running simulation. Please go to the Simulation tab and click \"reset\" first" unit)
  -- else do
  selectView Simulation
  void $ toSimulation $ Simulation.handleAction settings (ST.SetEditorText code)

handleAction settings (HandleBlocklyMessage CodeChange) = do
  -- FIXME: remove
  liftEffect $ Console.log "unsaved changes because Blockly event"
  assign _hasUnsavedChanges true

handleAction _ (HandleActusBlocklyMessage ActusBlockly.Initialized) = pure unit

handleAction settings (HandleActusBlocklyMessage (ActusBlockly.CurrentTerms flavour terms)) = do
  let
    parsedTermsEither = AMB.parseActusJsonCode terms
  case parsedTermsEither of
    Left e -> void $ query _actusBlocklySlot unit (ActusBlockly.SetError ("Couldn't parse contract-terms - " <> (show e)) unit)
    Right parsedTerms -> do
      result <- case flavour of
        ActusBlockly.FS -> runAjax $ flip runReaderT settings $ (Server.postApiActusGenerate parsedTerms)
        ActusBlockly.F -> runAjax $ flip runReaderT settings $ (Server.postApiActusGeneratestatic parsedTerms)
      case result of
        Success contractAST -> do
          selectView Simulation
          void $ toSimulation $ Simulation.handleAction settings (ST.SetEditorText contractAST)
        Failure e -> void $ query _actusBlocklySlot unit (ActusBlockly.SetError ("Server error! " <> (showErrorDescription (runAjaxError e).description)) unit)
        _ -> void $ query _actusBlocklySlot unit (ActusBlockly.SetError "Unknown server error!" unit)

-- QUESTION: How does this relates to the handleGistAction?
-- the save the project we use the PublishGist action and I thought that when we loaded
-- we used the LoadGist action, but it's actually this one.
-- FIXME probably add preventAccidentalNavigation
handleAction s (ProjectsAction action@(Projects.LoadProject lang gistId)) = do
  assign _createGistResult Loading
  res <-
    runExceptT
      $ do
          gist <- flip runReaderT s $ getApiGistsByGistId gistId
          lift $ loadGist gist
          pure gist
  case res of
    Right gist -> do
      modify_
        ( set _createGistResult (Success gist)
            <<< set _showModal Nothing
            <<< set _hasUnsavedChanges false
        )
    Left error -> do
      assign _createGistResult $ Failure error
      assign (_projects <<< Projects._projects) (Failure "Failed to load gist")
  toProjects $ Projects.handleAction s action
  selectView $ selectLanguageView lang

handleAction s (ProjectsAction action) = toProjects $ Projects.handleAction s action

handleAction s action@(NewProjectAction (NewProject.CreateProject lang)) =
  preventAccidentalNavigation s action do
    description <- use (_newProject <<< NewProject._projectName)
    modify_
      ( set _projectName description
          <<< set _gistId Nothing
          <<< set _createGistResult NotAsked
      )
    liftEffect $ LocalStorage.setItem gistIdLocalStorageKey mempty
    -- reset all the editors
    toHaskellEditor $ HaskellEditor.editorSetValue mempty
    liftEffect $ LocalStorage.setItem bufferLocalStorageKey mempty
    toJavascriptEditor $ JavascriptEditor.editorSetValue mempty
    liftEffect $ LocalStorage.setItem jsBufferLocalStorageKey mempty
    toSimulation $ Simulation.editorSetValue mempty
    liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey mempty
    void $ query _blocklySlot unit (Blockly.SetCode mempty unit)
    -- set the appropriate editor
    case lang of
      Haskell ->
        for_ (Map.lookup "Example" StaticData.demoFiles) \contents -> do
          toHaskellEditor $ HaskellEditor.editorSetValue HE.example
          liftEffect $ LocalStorage.setItem bufferLocalStorageKey HE.example
      Javascript ->
        for_ (Map.lookup "Example" StaticData.demoFilesJS) \contents -> do
          toJavascriptEditor $ JavascriptEditor.editorSetValue JE.example
          liftEffect $ LocalStorage.setItem jsBufferLocalStorageKey JE.example
      Marlowe -> do
        toSimulation $ Simulation.editorSetValue "?new_contract"
        liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey "?new_contract"
      _ -> pure unit
    selectView $ selectLanguageView lang
    modify_
      ( set (_simulationState <<< ST._source) lang
          <<< set _showModal Nothing
          <<< set _hasUnsavedChanges false
      )
    -- FIXME: remove
    liftEffect $ Console.log $ "New project _hasUnsavedChanges false " <> show lang

handleAction s (NewProjectAction action) = toNewProject $ NewProject.handleAction s action

-- FIXME probably add preventAccidentalNavigation
handleAction s (DemosAction action@(Demos.LoadDemo lang (Demos.Demo key))) = do
  case lang of
    Haskell -> for_ (Map.lookup key StaticData.demoFiles) \contents -> HaskellEditor.editorSetValue contents
    Javascript ->
      for_ (Map.lookup key StaticData.demoFilesJS) \contents -> do
        toJavascriptEditor $ JavascriptEditor.editorSetValue contents
        liftEffect $ LocalStorage.setItem jsBufferLocalStorageKey contents
    Marlowe -> do
      for_ (preview (ix key) StaticData.marloweContracts) \contents -> do
        Simulation.editorSetValue contents
    Blockly -> do
      for_ (preview (ix key) StaticData.marloweContracts) \contents -> do
        void $ query _blocklySlot unit (Blockly.SetCode contents unit)
    Actus -> pure unit
  assign _showModal Nothing
  selectView $ selectLanguageView lang

handleAction s (RenameAction action@Rename.SaveProject) = do
  projectName <- use (_rename <<< Rename._projectName)
  modify_
    ( set _projectName projectName
        <<< set _showModal Nothing
    )
  toRename $ Rename.handleAction s action

handleAction s (RenameAction action) = toRename $ Rename.handleAction s action

handleAction s (SaveAsAction action@SaveAs.SaveProject) = do
  currentName <- use _projectName
  currentGistId <- use _gistId
  projectName <- use (_saveAs <<< SaveAs._projectName)
  modify_
    ( set _gistId Nothing
        <<< set _projectName projectName
    )
  handleGistAction s PublishGist
  res <- peruse (_createGistResult <<< _Success)
  case res of
    Just gist -> do
      liftEffect $ LocalStorage.setItem gistIdLocalStorageKey (gist ^. (gistId <<< _GistId))
      modify_
        ( set _showModal Nothing
            <<< set _hasUnsavedChanges false
        )
    Nothing ->
      modify_
        ( set (_saveAs <<< SaveAs._error) (Just "Could not save project")
            <<< set _projectName currentName
            <<< set _gistId currentGistId
        )
  toSaveAs $ SaveAs.handleAction s action

handleAction s (SaveAsAction action) = toSaveAs $ SaveAs.handleAction s action

handleAction settings CheckAuthStatus = do
  checkAuthStatus settings

handleAction settings (GistAction subEvent) = handleGistAction settings subEvent

handleAction settings (OpenModal OpenProject) = do
  assign _showModal $ Just OpenProject
  toProjects $ Projects.handleAction settings Projects.LoadProjects

handleAction _ (OpenModal RenameProject) = do
  currentName <- use _projectName
  assign (_rename <<< Rename._projectName) currentName
  assign _showModal $ Just RenameProject

handleAction _ (OpenModal modalView) = assign _showModal $ Just modalView

handleAction _ CloseModal = assign _showModal Nothing

handleAction _ (ChangeProjectName name) = assign _projectName name

handleAction settings (OpenLoginPopup intendedAction) = do
  authRole <- liftAff openLoginPopup
  handleAction settings CloseModal
  assign (_authStatus <<< _Success <<< authStatusAuthRole) authRole
  case authRole of
    Anonymous -> pure unit
    GithubUser -> handleAction settings intendedAction

handleAction settings (ConfirmUnsavedNavigationAction intendedAction modalAction) = do
  toConfirmUnsavedNavigation intendedAction $ ConfirmUnsavedNavigation.handleAction settings modalAction
  handleAction settings CloseModal
  case modalAction of
    ConfirmUnsavedNavigation.Cancel -> pure unit
    ConfirmUnsavedNavigation.DontSaveProject -> do
      liftEffect $ Console.log "DontSaveProject"
      -- FIXME: this currently is never ending loop, need to comunicate
      -- with the preventNavigation that I want to do the action anyway
      -- The only way I can think of at the time is to put a boolean in the
      -- state
      handleAction settings intendedAction
    ConfirmUnsavedNavigation.SaveProject -> do
      liftEffect $ Console.log "SaveProject"
      state <- H.get
      -- FIXME: This was taken from the view, from the gistModal helper. I think we should
      -- refactor into a Save Action that does this check and receives a Maybe Action as
      -- a continuation
      if has (_authStatus <<< _Success <<< authStatusAuthRole <<< _GithubUser) state then do
        handleAction settings $ GistAction PublishGist
        handleAction settings intendedAction
      else
        handleAction settings $ OpenModal $ GithubLogin $ ConfirmUnsavedNavigationAction intendedAction modalAction

sendToSimulation :: forall m. MonadAff m => SPSettings_ SPParams_ -> Lang -> String -> HalogenM State Action ChildSlots Void m Unit
sendToSimulation settings language contract = do
  assign (_simulationState <<< _source) language
  selectView Simulation
  void $ toSimulation
    $ do
        Simulation.handleAction settings (ST.SetEditorText contract)
        Simulation.handleAction settings ST.ResetContract

selectLanguageView :: Lang -> View
selectLanguageView = case _ of
  Haskell -> HaskellEditor
  Marlowe -> Simulation
  Blockly -> BlocklyEditor
  Javascript -> JSEditor
  Actus -> ActusBlocklyEditor

routeToView :: Route -> Maybe View
routeToView { subroute } = case subroute of
  Router.Home -> Just HomePage
  Router.Simulation -> Just Simulation
  Router.HaskellEditor -> Just HaskellEditor
  Router.JSEditor -> Just JSEditor
  Router.ActusBlocklyEditor -> Just ActusBlocklyEditor
  Router.Blockly -> Just BlocklyEditor
  Router.Wallets -> Just WalletEmulator
  Router.GithubAuthCallback -> Nothing

viewToRoute :: View -> Router.SubRoute
viewToRoute = case _ of
  HomePage -> Router.Home
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

showErrorDescription (ResponseFormatError err) = "ResponseFormatError: " <> err

showErrorDescription (ConnectionError err) = "ConnectionError: " <> err

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM State Action ChildSlots Void m) a ->
  HalogenM State Action ChildSlots Void m (WebData a)
runAjax action = RemoteData.fromEither <$> runExceptT action

------------------------------------------------------------
checkAuthStatus :: forall m. MonadAff m => SPSettings_ SPParams_ -> HalogenM State Action ChildSlots Void m Unit
checkAuthStatus settings = do
  assign _authStatus Loading
  authResult <- runAjax $ runReaderT Server.getApiOauthStatus settings
  assign _authStatus authResult

handleGistAction ::
  forall m.
  MonadAff m =>
  MonadEffect m =>
  SPSettings_ SPParams_ -> GistAction -> HalogenM State Action ChildSlots Void m Unit
handleGistAction settings PublishGist = do
  description <- use _projectName
  let
    pruneEmpty :: forall a. Eq a => Monoid a => Maybe a -> Maybe a
    pruneEmpty (Just v)
      | v == mempty = Nothing

    pruneEmpty m = m

    -- playground is a meta-data file that we currently just use as a tag to check if a gist is a marlowe playground gist
    playground = "{}"
  marlowe <- pruneEmpty <$> toSimulation Simulation.editorGetValue
  haskell <- pruneEmpty <$> HaskellEditor.editorGetValue
  blockly <- pruneEmpty <$> query _blocklySlot unit (H.request Blockly.GetWorkspace)
  javascript <- pruneEmpty <$> (toJavascriptEditor JavascriptEditor.editorGetValue)
  actus <- pruneEmpty <$> query _actusBlocklySlot unit (H.request ActusBlockly.GetWorkspace)
  let
    files = { playground, marlowe, haskell, blockly, javascript, actus }

    newGist = mkNewGist description files
  void
    $ runMaybeT do
        mGist <- use _gistId
        assign _createGistResult Loading
        newResult <-
          lift
            $ case mGist of
                Nothing -> runAjax $ flip runReaderT settings $ Server.postApiGists newGist
                Just gistId -> runAjax $ flip runReaderT settings $ Server.patchApiGistsByGistId newGist gistId
        assign _createGistResult newResult
        gistId <- hoistMaybe $ preview (_Success <<< gistId) newResult
        modify_
          ( set _gistId (Just gistId)
              <<< set _loadGistResult (Right NotAsked)
              <<< set _hasUnsavedChanges false
          )

handleGistAction _ (SetGistUrl url) = do
  case Gists.parseGistUrl url of
    Right newGistUrl ->
      modify_
        ( set _createGistResult NotAsked
            <<< set _loadGistResult (Right NotAsked)
            <<< set _gistId (Just newGistUrl)
        )
    Left _ -> pure unit

handleGistAction settings LoadGist = do
  res <-
    runExceptT
      $ do
          eGistId <- ExceptT $ note "Gist Id not set." <$> use _gistId
          assign _loadGistResult $ Right Loading
          aGist <- lift $ runAjax $ flip runReaderT settings $ Server.getApiGistsByGistId eGistId
          assign _loadGistResult $ Right aGist
          gist <- ExceptT $ pure $ toEither (Left "Gist not loaded.") $ lmap errorToString aGist
          lift $ loadGist gist
          pure aGist
  modify_
    ( set _loadGistResult res
        <<< set _hasUnsavedChanges false
    )
  liftEffect $ Console.log "Gist loaded, unsaved changes should be false"
  where
  toEither :: forall e a. Either e a -> RemoteData e a -> Either e a
  toEither _ (Success a) = Right a

  toEither _ (Failure e) = Left e

  toEither x Loading = x

  toEither x NotAsked = x

loadGist ::
  forall m.
  MonadAff m =>
  MonadEffect m =>
  Gist ->
  HalogenM State Action ChildSlots Void m Unit
loadGist gist = do
  let
    { marlowe
    , haskell
    , blockly
    , javascript
    , actus
    } = playgroundFiles gist

    description = view gistDescription gist

    gistId' = preview gistId gist
  for_ haskell \s -> liftEffect $ LocalStorage.setItem bufferLocalStorageKey s
  for_ javascript \s -> liftEffect $ LocalStorage.setItem jsBufferLocalStorageKey s
  for_ marlowe \s -> liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey s
  assign _gistId gistId'
  assign _projectName description
  toSimulation $ Simulation.editorSetValue $ fromMaybe mempty marlowe
  HaskellEditor.editorSetValue (fromMaybe mempty haskell)
  for_ blockly \xml -> query _blocklySlot unit (Blockly.LoadWorkspace xml unit)
  toJavascriptEditor $ JavascriptEditor.editorSetValue $ fromMaybe mempty javascript
  for_ actus \xml -> query _actusBlocklySlot unit (ActusBlockly.LoadWorkspace xml unit)

------------------------------------------------------------
preventAccidentalNavigation ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action ->
  HalogenM State Action ChildSlots Void m Unit ->
  HalogenM State Action ChildSlots Void m Unit
preventAccidentalNavigation settings intendedAction guardedEffect = do
  let
    isEditorView = case _ of
      HaskellEditor -> true
      JSEditor -> true
      BlocklyEditor -> true
      ActusBlocklyEditor -> true
      -- TODO: currently simulation refers to the Marlowe editor.
      -- Once we separate the simulation from the editor, we need to revisit this
      Simulation -> true
      _ -> false
  currentView <- use _view
  wantsToSaveProject <- use (_confirmUnsavedNavigation <<< _wantsToSaveProject)
  hasUnsavedChanges <- use _hasUnsavedChanges
  -- FIXME remove console.log
  liftEffect $ Console.log $ "preventAccidentalNavigation: currentView " <> show currentView
  liftEffect $ Console.log $ "preventAccidentalNavigation: wantsToSaveProject " <> show wantsToSaveProject
  liftEffect $ Console.log $ "preventAccidentalNavigation: hasUnsavedChanges " <> show hasUnsavedChanges
  if isEditorView currentView && wantsToSaveProject && hasUnsavedChanges then do
    liftEffect $ Console.log "Dont forget to save "
    handleAction settings $ OpenModal $ ConfirmUnsavedNavigation intendedAction
  else do
    -- Once we do the guarded effect, we want to restore wantsToSaveProject to the default
    -- This prevents the user selecting no once, of never seeing the dialog again
    assign (_confirmUnsavedNavigation <<< _wantsToSaveProject) true
    guardedEffect

------------------------------------------------------------
selectView ::
  forall m action message.
  MonadEffect m =>
  View -> HalogenM State action ChildSlots message m Unit
selectView view = do
  -- FIXME: remove console.log
  currentView <- use _view
  liftEffect $ Console.log $ "selectView from " <> show currentView <> " to " <> show view
  liftEffect $ Routing.setHash (RD.print Router.route { subroute: viewToRoute view, gistId: Nothing })
  assign _view view
  liftEffect do
    window <- Web.window
    Window.scroll 0 0 window
  case view of
    HomePage -> pure unit
    Simulation -> do
      Simulation.editorResize
      Simulation.editorSetTheme
    HaskellEditor -> do
      HaskellEditor.editorResize
      void $ query _haskellEditorSlot unit (Monaco.SetTheme HM.daylightTheme.name unit)
    JSEditor -> do
      void $ query _jsEditorSlot unit (Monaco.Resize unit)
      void $ query _jsEditorSlot unit (Monaco.SetTheme HM.daylightTheme.name unit)
    BlocklyEditor -> void $ query _blocklySlot unit (Blockly.Resize unit)
    WalletEmulator -> pure unit
    ActusBlocklyEditor -> void $ query _actusBlocklySlot unit (ActusBlockly.Resize unit)
