module MainFrame (mainFrame) where

import API (_RunResult)
import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceMessage(TextChanged))
import Ace.Types (Editor, Annotation)
import Analytics (Event, defaultEvent, trackEvent)
import Bootstrap (active, btn, btnGroup, btnInfo, btnPrimary, btnSmall, colXs12, colSm6, colSm5, container, container_, empty, hidden, listGroupItem_, listGroup_, navItem_, navLink, navTabs_, noGutters, pullRight, row, justifyContentBetween)
import Control.Bind (bindFlipped, map, void, when)
import Control.Monad.Except (runExceptT)
import Control.Monad.Maybe.Trans (MaybeT(..), lift, runMaybeT)
import Control.Monad.Reader.Class (class MonadAsk)
import Control.Monad.State.Trans (class MonadState)
import Data.Array (catMaybes, delete, snoc)
import Data.Array as Array
import Data.Either (Either(..), note)
import Data.Function (flip)
import Data.Json.JsonEither (JsonEither(..))
import Data.Lens (_Just, assign, modifying, over, preview, use, view)
import Data.List.NonEmpty as NEL
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing))
import Data.Newtype (unwrap)
import Data.String as String
import Data.Tuple (Tuple(Tuple))
import Data.Tuple.Nested ((/\))
import Editor (editorPane)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Foreign.Class (decode)
import Foreign.JSON (parseJSON)
import Gist (gistFileContent, gistId)
import Gists (parseGistUrl, gistControls)
import Halogen (Component, ComponentHTML)
import Halogen as H
import Halogen.Blockly (BlocklyMessage(..), blockly)
import Halogen.HTML (ClassName(ClassName), HTML, a, button, code_, div, div_, h1, pre, slot, strong_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, disabled, href)
import Halogen.Query (HalogenM)
import Language.Haskell.Interpreter (SourceCode(SourceCode), InterpreterError(CompilationErrors, TimeoutError), CompilationError(CompilationError, RawError), InterpreterResult(InterpreterResult), _InterpreterResult)
import Marlowe (SPParams_)
import Marlowe.Blockly as MB
import Marlowe.Gists (mkNewGist, playgroundGistFile)
import Marlowe.Pretty (pretty)
import Marlowe.Semantics (ChoiceId, Input(..), inBounds)
import MonadApp (class MonadApp, applyTransactions, checkContractForWarnings, getGistByGistId, getOauthStatus, haskellEditorGetValue, haskellEditorGotoLine, haskellEditorSetAnnotations, haskellEditorSetValue, marloweEditorGetValue, marloweEditorSetValue, patchGistByGistId, postContractHaskell, postGist, preventDefault, readFileFromDragEvent, resetContract, resizeBlockly, runHalogenApp, saveBuffer, saveInitialState, saveMarloweBuffer, setBlocklyCode, updateContractInState, updateMarloweState)
import Network.RemoteData (RemoteData(..), _Success, isLoading, isSuccess)
import Prelude (Unit, add, bind, const, discard, not, one, pure, show, unit, zero, ($), (-), (<$>), (<<<), (<>), (==), (||))
import Servant.PureScript.Settings (SPSettings_)
import Simulation (simulationPane)
import StaticData as StaticData
import Types (ActionInput(..), ChildSlots, FrontendState(FrontendState), HAction(..), HQuery(..), View(..), WebsocketMessage, _analysisState, _authStatus, _blocklySlot, _compilationResult, _createGistResult, _currentContract, _gistUrl, _marloweState, _oldContract, _pendingInputs, _possibleActions, _result, _slot, _view, emptyMarloweState)
import WebSocket (WebSocketResponseMessage(..))

initialState :: FrontendState
initialState =
  FrontendState
    { view: HaskellEditor
    , compilationResult: NotAsked
    , marloweCompileResult: Right unit
    , authStatus: NotAsked
    , createGistResult: NotAsked
    , marloweState: NEL.singleton (emptyMarloweState zero)
    , oldContract: Nothing
    , gistUrl: Nothing
    , blocklyState: Nothing
    , analysisState: NotAsked
    }

------------------------------------------------------------
mainFrame ::
  forall m.
  MonadAff m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  Component HTML HQuery Unit WebsocketMessage m
mainFrame =
  H.mkComponent
    { initialState: const initialState
    , render
    , eval: H.mkEval
        { handleQuery
        , handleAction: handleActionWithAnalyticsTracking
        , receive: const Nothing
        , initialize: Just $ CheckAuthStatus
        , finalize: Nothing
        }
    }

handleActionWithAnalyticsTracking ::
  forall m.
  MonadAff m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  HAction -> HalogenM FrontendState HAction ChildSlots WebsocketMessage m Unit
handleActionWithAnalyticsTracking action = do
  liftEffect $ analyticsTracking action
  runHalogenApp $ handleAction action

analyticsTracking :: HAction -> Effect Unit
analyticsTracking action = do
  case toEvent action of
    Nothing -> pure unit
    Just event -> trackEvent event

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
toEvent :: HAction -> Maybe Event
toEvent (HandleEditorMessage _) = Nothing

toEvent (HandleDragEvent _) = Nothing

toEvent (HandleDropEvent _) = Just $ defaultEvent "DropScript"

toEvent (MarloweHandleEditorMessage _) = Nothing

toEvent (MarloweHandleDragEvent _) = Nothing

toEvent (MarloweHandleDropEvent _) = Just $ defaultEvent "MarloweDropScript"

toEvent CheckAuthStatus = Nothing

toEvent PublishGist = Just $ (defaultEvent "Publish") {label = Just "Gist"}

toEvent (SetGistUrl _) = Nothing

toEvent LoadGist = Just $ (defaultEvent "LoadGist") {category = Just "Gist"}

toEvent (ChangeView view) = Just $ (defaultEvent "View") {label = Just $ show view}

toEvent (LoadScript script) = Just $ (defaultEvent "LoadScript") {label = Just script}

toEvent (LoadMarloweScript script) = Just $ (defaultEvent "LoadMarloweScript") {label = Just script}

toEvent CompileProgram = Just $ defaultEvent "CompileProgram"

toEvent SendResult = Nothing

toEvent (ScrollTo _) = Nothing

toEvent ApplyTransaction = Just $ defaultEvent "ApplyTransaction"

toEvent NextSlot = Just $ defaultEvent "NextBlock"

toEvent (AddInput _ _ _) = Nothing

toEvent (RemoveInput _ _) = Nothing

toEvent (SetChoice _ _) = Nothing

toEvent ResetSimulator = Nothing

toEvent Undo = Just $ defaultEvent "Undo"

toEvent (HandleBlocklyMessage _) = Nothing

toEvent SetBlocklyCode = Nothing

toEvent AnalyseContract = Nothing

handleQuery :: forall m a. MonadState FrontendState m => HQuery a -> m (Maybe a)

handleQuery (ReceiveWebsocketMessage msg next) = do
  let msgDecoded = unwrap <<< runExceptT $ do
                                            f <- parseJSON msg
                                            decode f
  case msgDecoded of
    Left err -> assign _analysisState <<< Failure $ show $ msg
    Right (OtherError err) -> assign _analysisState $ Failure err
    Right (CheckForWarningsResult result) -> assign _analysisState $ Success result
  pure $ Just next

handleAction ::
  forall m.
  MonadAsk (SPSettings_ SPParams_) m =>
  MonadApp m =>
  MonadState FrontendState m =>
  HAction -> m Unit
handleAction (HandleEditorMessage (TextChanged text)) = saveBuffer text

handleAction (HandleDragEvent event) = preventDefault event

handleAction (HandleDropEvent event) = do
  preventDefault event
  contents <- readFileFromDragEvent event
  haskellEditorSetValue contents (Just 1)

handleAction (MarloweHandleEditorMessage (TextChanged text)) = do
  saveMarloweBuffer text
  updateContractInState text

handleAction (MarloweHandleDragEvent event) = preventDefault event

handleAction (MarloweHandleDropEvent event) = do
  preventDefault event
  contents <- readFileFromDragEvent event
  marloweEditorSetValue contents (Just 1)
  updateContractInState contents

handleAction CheckAuthStatus = do
  assign _authStatus Loading
  authResult <- getOauthStatus
  assign _authStatus authResult

handleAction PublishGist = do
  mContents <- haskellEditorGetValue
  case mkNewGist (SourceCode <$> mContents) of
    Nothing -> pure unit
    Just newGist -> do
      mGist <- use _createGistResult
      assign _createGistResult Loading
      newResult <- case preview (_Success <<< gistId) mGist of
        Nothing -> postGist newGist
        Just gistId -> patchGistByGistId newGist gistId
      assign _createGistResult newResult
      case preview (_Success <<< gistId) newResult of
        Nothing -> pure unit
        Just gistId -> assign _gistUrl (Just (unwrap gistId))

handleAction (SetGistUrl newGistUrl) = assign _gistUrl (Just newGistUrl)

handleAction LoadGist = do
  eGistId <- (bindFlipped parseGistUrl <<< note "Gist Url not set.") <$> use _gistUrl
  case eGistId of
    Left err -> pure unit
    Right gistId -> do
      assign _createGistResult Loading
      aGist <- getGistByGistId gistId
      assign _createGistResult aGist
      case aGist of
        Success gist -> do
          -- Load the source, if available.
          case preview (_Just <<< gistFileContent <<< _Just) (playgroundGistFile gist) of
            Nothing -> pure unit
            Just contents -> do
              haskellEditorSetValue contents (Just 1)
              saveBuffer contents
              assign _compilationResult NotAsked
              pure unit
        _ -> pure unit

handleAction (ChangeView view) = do
  assign _view view
  void resizeBlockly

handleAction (LoadScript key) = do
  case Map.lookup key StaticData.demoFiles of
    Nothing -> pure unit
    Just contents -> do
      haskellEditorSetValue contents (Just 1)

handleAction (LoadMarloweScript key) = do
  case Map.lookup key StaticData.marloweContracts of
    Nothing -> pure unit
    Just contents -> do
      marloweEditorSetValue contents (Just 1)
      updateContractInState contents
      resetContract

handleAction CompileProgram = do
  mContents <- haskellEditorGetValue
  case mContents of
    Nothing -> pure unit
    Just contents -> do
      assign _compilationResult Loading
      result <- postContractHaskell $ SourceCode contents
      assign _compilationResult result
      -- Update the error display.
      haskellEditorSetAnnotations
        $ case result of
            Success (JsonEither (Left errors)) -> toAnnotations errors
            _ -> []

handleAction SendResult = do
  mContract <- use _compilationResult
  let
    contract = case mContract of
      Success (JsonEither (Right x)) -> view (_InterpreterResult <<< _result <<< _RunResult) x
      _ -> ""
  marloweEditorSetValue contract (Just 1)
  updateContractInState contract
  resetContract
  assign _view (Simulation)

handleAction (ScrollTo {row, column}) = haskellEditorGotoLine row (Just column)

handleAction ApplyTransaction = do
  saveInitialState
  applyTransactions
  mCurrContract <- use _currentContract
  case mCurrContract of
    Just currContract -> do
      marloweEditorSetValue (show $ pretty currContract) (Just 1)
    Nothing -> pure unit

handleAction NextSlot = do
  saveInitialState
  updateMarloweState (over _slot (add one))

handleAction (AddInput person input bounds) = do
  when validInput do
    updateMarloweState (over _pendingInputs ((flip snoc) (Tuple input person)))
    currContract <- marloweEditorGetValue
    case currContract of
      Nothing -> pure unit
      Just contract -> updateContractInState contract
  where
    validInput = case input of
      (IChoice _ chosenNum) -> inBounds chosenNum bounds
      _ -> true

handleAction (RemoveInput person input) = do
  updateMarloweState (over _pendingInputs (delete (Tuple input person)))
  currContract <- marloweEditorGetValue
  case currContract of
    Nothing -> pure unit
    Just contract -> updateContractInState contract

handleAction (SetChoice choiceId chosenNum) =
  updateMarloweState (over _possibleActions ((map <<< map) (updateChoice choiceId)))
  where
    updateChoice :: ChoiceId -> ActionInput -> ActionInput
    updateChoice wantedChoiceId input@(ChoiceInput currentChoiceId bounds _) = if wantedChoiceId == currentChoiceId then ChoiceInput choiceId bounds chosenNum else input
    updateChoice _ input = input

handleAction ResetSimulator = do
  oldContract <- use _oldContract
  currContract <- marloweEditorGetValue
  let
    newContract = case oldContract of
      Just x -> x
      Nothing -> case currContract of
        Nothing -> ""
        Just y -> y
  marloweEditorSetValue newContract (Just 1)
  resetContract

handleAction Undo = do
  modifying _marloweState removeState
  mCurrContract <- use _currentContract
  case mCurrContract of
    Just currContract -> marloweEditorSetValue (show $ pretty currContract) (Just 1)
    Nothing -> pure unit
  where
  removeState ms =
    let
      {head, tail} = NEL.uncons ms
    in
      case NEL.fromList tail of
        Nothing -> ms
        Just netail -> netail

handleAction (HandleBlocklyMessage Initialized) = pure unit

handleAction (HandleBlocklyMessage (CurrentCode code)) = do
      marloweEditorSetValue code (Just 1)
      assign _view Simulation

handleAction SetBlocklyCode = void $ runMaybeT do
    source <- MaybeT marloweEditorGetValue
    lift do
      setBlocklyCode source
      assign _view BlocklyEditor
    MaybeT resizeBlockly

handleAction AnalyseContract = do
  currContract <- use _currentContract
  case currContract of
    Nothing -> pure unit
    Just contract -> do
      checkContractForWarnings (show contract)
      assign _analysisState Loading

------------------------------------------------------------
showCompilationErrorAnnotations ::
  Array Annotation ->
  Editor ->
  Effect Unit
showCompilationErrorAnnotations annotations editor = do
  session <- Editor.getSession editor
  Session.setAnnotations annotations session

toAnnotations :: InterpreterError -> Array Annotation
toAnnotations (TimeoutError _) = []

toAnnotations (CompilationErrors errors) = catMaybes (toAnnotation <$> errors)

toAnnotation :: CompilationError -> Maybe Annotation
toAnnotation (RawError _) = Nothing

toAnnotation (CompilationError {row, column, text}) =
  Just
    { "type": "error"
    , row: row - 1
    , column
    , text: String.joinWith "\\n" text
    }

render ::
  forall m.
  MonadAff m =>
  FrontendState ->
  ComponentHTML HAction ChildSlots m
render state =
  let
    stateView = view _view state
  in
    div [class_ $ ClassName "main-frame"]
      [ container_
          [ mainHeader
          , div [classes [row, noGutters, justifyContentBetween]]
              [ div [classes [colXs12, colSm6]] [mainTabBar stateView]
              , div [classes [colXs12, colSm5]] [gistControls (unwrap state)]
              ]
          ]
      , viewContainer stateView HaskellEditor
          [ loadScriptsPane
          , editorPane defaultContents (unwrap <$> (view _compilationResult state))
          , resultPane state
          ]
      , viewContainer stateView Simulation
          [ simulationPane state
          ]
      , viewContainer stateView BlocklyEditor
          [ slot _blocklySlot unit (blockly blockDefinitions) unit (Just <<< HandleBlocklyMessage)
          , MB.toolbox
          , MB.workspaceBlocks
          ]
      ]
  where
  defaultContents = Map.lookup "Escrow" StaticData.demoFiles

  blockDefinitions = MB.blockDefinitions

loadScriptsPane :: forall p. HTML p HAction
loadScriptsPane =
  div [class_ $ ClassName "mb-3"]
    ( Array.cons
      ( strong_
        [ text "Demos: "
        ]
      ) (loadScriptButton <$> Array.fromFoldable (Map.keys StaticData.demoFiles))
    )

loadScriptButton :: forall p. String -> HTML p HAction
loadScriptButton key =
  button
    [ classes [btn, btnInfo, btnSmall]
    , onClick $ const $ Just $ LoadScript key
    ] [text key]

viewContainer :: forall p i. View -> View -> Array (HTML p i) -> HTML p i
viewContainer currentView targetView = if currentView == targetView
  then div [classes [container]]
  else div [classes [container, hidden]]

mainHeader :: forall p. HTML p HAction
mainHeader =
  div_
    [ div [classes [btnGroup, pullRight]] (makeLink <$> links)
    , h1 [class_ $ ClassName "main-title"] [text "Marlowe Playground"]
    ]
  where
  links =
    [ Tuple "Tutorial" "./tutorial"
    , Tuple "Privacy" "https://static.iohk.io/docs/data-protection/iohk-data-protection-gdpr-policy.pdf"
    ]

  makeLink (Tuple name link) =
    a
      [ classes
          [ btn
          , btnSmall
          ]
      , href link
      ]
      [ text name
      ]

mainTabBar :: forall p. View -> HTML p HAction
mainTabBar activeView = navTabs_ (mkTab <$> tabs)
  where
  tabs =
    [ HaskellEditor /\ "Haskell Editor"
    , Simulation /\ "Simulation"
    , BlocklyEditor /\ "Blockly"
    ]

  mkTab (link /\ title) =
    navItem_
      [ a
          [ classes
              $ [ navLink
                ]
              <> activeClass
          , onClick $ const $ Just $ ChangeView link
          ]
          [ text title
          ]
      ]
    where
    activeClass = if link == activeView
      then
        [ active
        ]
      else []

resultPane :: forall p. FrontendState -> HTML p HAction
resultPane state =
  let
    compilationResult = view _compilationResult state
  in
    case compilationResult of
      Success (JsonEither (Right (InterpreterResult result))) ->
        listGroup_
          [ listGroupItem_
              [ div_
                  [ button
                      [ classes
                          [ btn
                          , btnPrimary
                          , ClassName "float-right"
                          ]
                      , onClick $ const $ Just SendResult
                      , disabled (isLoading compilationResult || (not isSuccess) compilationResult)
                      ] [text "Send to Simulator"]
                  , code_
                      [ pre [class_ $ ClassName "success-code"] [text (unwrap result.result)]
                      ]
                  ]
              ]
          ]
      _ -> empty
