module MainFrame (mainFrame) where

import API (_RunResult)
import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceMessage(TextChanged))
import Ace.Types (Editor, Annotation)
import Analytics (Event, defaultEvent, trackEvent)
import Bootstrap
  ( active
  , btn
  , btnGroup
  , btnInfo
  , btnPrimary
  , btnSmall
  , colXs12
  , colSm6
  , colSm5
  , container
  , container_
  , empty
  , hidden
  , listGroupItem_
  , listGroup_
  , navItem_
  , navLink
  , navTabs_
  , noGutters
  , pullRight
  , row
  , justifyContentBetween
  )
import Control.Bind (bindFlipped)
import Control.Monad.Reader.Class (class MonadAsk)
import Control.Monad.State.Trans (class MonadState)
import Data.Array (catMaybes, delete, snoc)
import Data.Array as Array
import Data.Either (Either(..), note)
import Data.Function (flip)
import Data.Lens (_Just, assign, modifying, over, preview, set, use, view)
import Data.Lens.Index (ix)
import Data.List.NonEmpty as NEL
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing))
import Data.Newtype (unwrap)
import Data.RawJson (JsonEither(..))
import Data.Set as Set
import Data.String as String
import Data.Tuple (Tuple(Tuple))
import Data.Tuple.Nested ((/\))
import Editor (editorPane)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Gist (gistFileContent, gistId)
import Gists (parseGistUrl, gistControls)
import Halogen (Component, action)
import Halogen as H
import Halogen.Component (ParentHTML)
import Halogen.HTML (ClassName(ClassName), HTML, a, button, code_, div, div_, h1, pre, strong_, text)
import Halogen.HTML.Events (onClick, input_)
import Halogen.HTML.Properties (class_, classes, href, disabled)
import Halogen.Query (HalogenM)
import Language.Haskell.Interpreter (SourceCode(SourceCode), InterpreterError(CompilationErrors, TimeoutError), CompilationError(CompilationError, RawError), InterpreterResult(InterpreterResult), _InterpreterResult)
import Marlowe.Pretty (pretty)
import Marlowe.Semantics (MApplicationResult(MCouldNotApply, MSuccessfullyApplied), applyTransaction)
import Marlowe.Test (_blockNumber)
import Marlowe.Types (IdChoice(IdChoice))
import Meadow (SPParams_)
import Meadow.Gists (mkNewGist, playgroundGistFile)
import MonadApp
  ( class MonadApp
  , saveMarloweBuffer
  , getGistByGistId
  , patchGistByGistId
  , postGist
  , postContractHaskell
  , getOauthStatus
  , saveBuffer
  , runHalogenApp
  , marloweEditorGetValue
  , marloweEditorSetValue
  , editorGetValue
  , editorGotoLine
  , editorSetAnnotations
  , editorSetValue
  , emptyMarloweState
  , extendWith
  , preventDefault
  , readFileFromDragEvent
  , resetContract
  , saveInitialState
  , updateContractInState
  , updateMarloweState
  , updateState
  )
import Network.RemoteData (RemoteData(Success, Loading, NotAsked), _Success, isLoading, isSuccess)
import Prelude (type (~>), Unit, Void, add, bind, const, discard, identity, not, one, pure, show, unit, (#), ($), (-), (<$>), (<<<), (<>), (==), (||))
import Servant.PureScript.Settings (SPSettings_)
import Simulation (simulationPane)
import StaticData as StaticData
import Types
  ( ChildQuery
  , ChildSlot
  , FrontendState(FrontendState)
  , MarloweState
  , Query(SendResult, ChangeView, LoadScript, Undo, ResetSimulator, SetOracleBn, SetOracleVal, SetChoice, RemoveAnyInput, AddAnyInput, NextBlock, ApplyTransaction, SetSignature, ScrollTo, CompileProgram, LoadMarloweScript, LoadGist, SetGistUrl, PublishGist, CheckAuthStatus, MarloweHandleDropEvent, MarloweHandleDragEvent, MarloweHandleEditorMessage, HandleDropEvent, HandleDragEvent, HandleEditorMessage)
  , View(Simulation, Editor)
  , _authStatus
  , _blockNum
  , _choiceData
  , _compilationResult
  , _contract
  , _createGistResult
  , _currentContract
  , _currentInput
  , _currentTransaction
  , _gistUrl
  , _inputs
  , _marloweState
  , _moneyInContract
  , _oldContract
  , _oracleData
  , _result
  , _signatures
  , _state
  , _transaction
  , _value
  , _view
  )

initialState :: FrontendState
initialState =
  FrontendState
    { view: Editor
    , compilationResult: NotAsked
    , marloweCompileResult: Right unit
    , authStatus: NotAsked
    , createGistResult: NotAsked
    , marloweState: NEL.singleton emptyMarloweState
    , oldContract: Nothing
    , gistUrl: Nothing
    }

------------------------------------------------------------
mainFrame ::
  forall m.
  MonadAff m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  Component HTML Query Unit Void m
mainFrame =
  H.lifecycleParentComponent
    { initialState: const initialState
    , render
    , eval: evalWithAnalyticsTracking
    , receiver: const Nothing
    , initializer: Just $ H.action $ CheckAuthStatus
    , finalizer: Nothing
    }

evalWithAnalyticsTracking ::
  forall m.
  MonadAff m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  Query
    ~> HalogenM FrontendState Query ChildQuery ChildSlot Void m
evalWithAnalyticsTracking query = do
  liftEffect $ analyticsTracking query
  runHalogenApp $ evalF query

analyticsTracking ::
  forall a.
  Query a ->
  Effect Unit
analyticsTracking query = do
  case toEvent query of
    Nothing -> pure unit
    Just event -> trackEvent event

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
toEvent ::
  forall a.
  Query a ->
  Maybe Event
toEvent (HandleEditorMessage _ _) = Nothing

toEvent (HandleDragEvent _ _) = Nothing

toEvent (HandleDropEvent _ _) = Just $ defaultEvent "DropScript"

toEvent (MarloweHandleEditorMessage _ _) = Nothing

toEvent (MarloweHandleDragEvent _ _) = Nothing

toEvent (MarloweHandleDropEvent _ _) = Just $ defaultEvent "MarloweDropScript"

toEvent (CheckAuthStatus _) = Nothing

toEvent (PublishGist _) = Just $ (defaultEvent "Publish") {label = Just "Gist"}

toEvent (SetGistUrl _ _) = Nothing

toEvent (LoadGist _) = Just $ (defaultEvent "LoadGist") {category = Just "Gist"}

toEvent (ChangeView view _) = Just $ (defaultEvent "View") {label = Just $ show view}

toEvent (LoadScript script a) = Just $ (defaultEvent "LoadScript") {label = Just script}

toEvent (LoadMarloweScript script a) = Just $ (defaultEvent "LoadMarloweScript") {label = Just script}

toEvent (CompileProgram a) = Just $ defaultEvent "CompileProgram"

toEvent (SendResult a) = Nothing

toEvent (ScrollTo _ _) = Nothing

toEvent (SetSignature _ _) = Nothing

toEvent (ApplyTransaction _) = Just $ defaultEvent "ApplyTransaction"

toEvent (NextBlock _) = Just $ defaultEvent "NextBlock"

toEvent (AddAnyInput _ _) = Nothing

toEvent (RemoveAnyInput _ _) = Nothing

toEvent (SetChoice _ _) = Nothing

toEvent (SetOracleVal _ _) = Nothing

toEvent (SetOracleBn _ _) = Nothing

toEvent (ResetSimulator _) = Nothing

toEvent (Undo _) = Just $ defaultEvent "Undo"

applyTransactionM :: MarloweState -> MarloweState
applyTransactionM oldState = case oldState.contract of
  Nothing -> oldState
  Just c -> case applyTransaction inps sigs bn st c mic of
    MSuccessfullyApplied {funds, state, contract} _ ->
      oldState
        # set (_transaction <<< _inputs) []
        # set (_transaction <<< _signatures) Map.empty
        # set (_state) state
        # set (_moneyInContract) funds
        # set (_contract) (Just contract)
    MCouldNotApply _ -> oldState
  where
  inps = Array.toUnfoldable (oldState.transaction.inputs)

  sigs = Set.fromFoldable (Map.keys (Map.filter identity (oldState.transaction.signatures)))

  bn = oldState.blockNum

  st = oldState.state

  mic = oldState.moneyInContract

evalF ::
  forall m.
  MonadAsk (SPSettings_ SPParams_) m =>
  MonadApp m =>
  MonadState FrontendState m =>
  Query ~> m
evalF (HandleEditorMessage (TextChanged text) next) = do
  saveBuffer text
  pure next

evalF (HandleDragEvent event next) = do
  preventDefault event
  pure next

evalF (HandleDropEvent event next) = do
  preventDefault event
  contents <- readFileFromDragEvent event
  editorSetValue contents (Just 1)
  pure next

evalF (MarloweHandleEditorMessage (TextChanged text) next) = do
  saveMarloweBuffer text
  updateContractInState text
  pure next

evalF (MarloweHandleDragEvent event next) = do
  preventDefault event
  pure next

evalF (MarloweHandleDropEvent event next) = do
  preventDefault event
  contents <- readFileFromDragEvent event
  editorSetValue contents (Just 1)
  updateContractInState contents
  pure next

evalF (CheckAuthStatus next) = do
  assign _authStatus Loading
  authResult <- getOauthStatus
  assign _authStatus authResult
  pure next

evalF (PublishGist next) = do
  mContents <- editorGetValue
  case mkNewGist (SourceCode <$> mContents) of
    Nothing -> pure next
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
      pure next

evalF (SetGistUrl newGistUrl next) = do
  assign _gistUrl (Just newGistUrl)
  pure next

evalF (LoadGist next) = do
  eGistId <- (bindFlipped parseGistUrl <<< note "Gist Url not set.") <$> use _gistUrl
  case eGistId of
    Left err -> pure next
    Right gistId -> do
      assign _createGistResult Loading
      aGist <- getGistByGistId gistId
      assign _createGistResult aGist
      case aGist of
        Success gist -> do
          -- Load the source, if available.
          case preview (_Just <<< gistFileContent <<< _Just) (playgroundGistFile gist) of
            Nothing -> pure next
            Just contents -> do
              editorSetValue contents (Just 1)
              saveBuffer contents
              assign _compilationResult NotAsked
              pure next
        _ -> pure next

evalF (ChangeView view next) = do
  assign _view view
  pure next

evalF (LoadScript key next) = do
  case Map.lookup key StaticData.demoFiles of
    Nothing -> pure next
    Just contents -> do
      editorSetValue contents (Just 1)
      pure next

evalF (LoadMarloweScript key next) = do
  case Map.lookup key StaticData.marloweContracts of
    Nothing -> pure next
    Just contents -> do
      editorSetValue contents (Just 1)
      updateContractInState contents
      resetContract
      pure next

evalF (CompileProgram next) = do
  mContents <- editorGetValue
  case mContents of
    Nothing -> pure next
    Just contents -> do
      assign _compilationResult Loading
      result <- postContractHaskell $ SourceCode contents
      assign _compilationResult result
      -- Update the error display.
      editorSetAnnotations
        $ case result of
            Success (JsonEither (Left errors)) -> toAnnotations errors
            _ -> []
      pure next

evalF (SendResult next) = do
  mContract <- use _compilationResult
  let
    contract = case mContract of
      Success (JsonEither (Right x)) -> view (_InterpreterResult <<< _result <<< _RunResult) x
      _ -> ""
  editorSetValue contract (Just 1)
  updateContractInState contract
  resetContract
  assign _view (Simulation)
  pure next

evalF (ScrollTo {row, column} next) = do
  editorGotoLine row (Just column)
  pure next

evalF (SetSignature {person, isChecked} next) = do
  modifying (_currentTransaction <<< _signatures) (Map.insert person isChecked)
  updateState
  pure next

evalF (ApplyTransaction next) = do
  saveInitialState
  modifying _marloweState (extendWith applyTransactionM)
  mCurrContract <- use _currentContract
  case mCurrContract of
    Just currContract -> do
      editorSetValue (show $ pretty currContract) (Just 1)
      updateState
      pure next
    Nothing -> pure next

evalF (NextBlock next) = do
  saveInitialState
  updateMarloweState (over _blockNum (add one))
  updateState
  pure next

evalF (AddAnyInput {person, anyInput} next) = do
  modifying (_currentTransaction <<< _inputs) ((flip snoc) anyInput)
  case person of
    Just per -> do
      modifying (_currentTransaction <<< _signatures) (Map.insert per true)
      updateState
      pure next
    Nothing -> do
      updateState
      pure next

evalF (RemoveAnyInput anyInput next) = do
  modifying (_currentTransaction <<< _inputs) (delete anyInput)
  updateState
  pure next

evalF (SetChoice {idChoice: (IdChoice {choice, person}), value} next) = do
  assign (_currentInput <<< _choiceData <<< ix person <<< ix choice) value
  updateState
  pure next

evalF (SetOracleVal {idOracle, value} next) = do
  assign (_currentInput <<< _oracleData <<< ix idOracle <<< _value) value
  updateState
  pure next

evalF (SetOracleBn {idOracle, blockNumber} next) = do
  assign (_currentInput <<< _oracleData <<< ix idOracle <<< _blockNumber) blockNumber
  updateState
  pure next

evalF (ResetSimulator next) = do
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
  pure next

evalF (Undo next) = do
  modifying _marloweState removeState
  mCurrContract <- use _currentContract
  case mCurrContract of
    Just currContract -> marloweEditorSetValue (show $ pretty currContract) (Just 1)
    Nothing -> pure unit
  pure next
  where
  removeState ms =
    let
      {head, tail} = NEL.uncons ms
    in
      case NEL.fromList tail of
        Nothing -> ms
        Just netail -> netail

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
  ParentHTML Query ChildQuery ChildSlot m
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
      , viewContainer stateView Editor
          $ [ loadScriptsPane
            , editorPane defaultContents (unwrap <$> (view _compilationResult state))
            , resultPane state
            ]
      , viewContainer stateView Simulation
          $ [ simulationPane state
            ]
      ]
  where
  defaultContents = Map.lookup "Escrow" StaticData.demoFiles

loadScriptsPane :: forall p. HTML p (Query Unit)
loadScriptsPane =
  div [class_ $ ClassName "mb-3"]
    ( Array.cons
      ( strong_
        [ text "Demos: "
        ]
      ) (loadScriptButton <$> Array.fromFoldable (Map.keys StaticData.demoFiles))
    )

loadScriptButton :: forall p. String -> HTML p (Query Unit)
loadScriptButton key =
  button
    [ classes [btn, btnInfo, btnSmall]
    , onClick $ input_ $ LoadScript key
    ] [text key]

viewContainer :: forall p i. View -> View -> Array (HTML p i) -> HTML p i
viewContainer currentView targetView = if currentView == targetView
  then div [classes [container]]
  else div [classes [container, hidden]]

mainHeader :: forall p. HTML p (Query Unit)
mainHeader =
  div_
    [ div [classes [btnGroup, pullRight]] (makeLink <$> links)
    , h1 [class_ $ ClassName "main-title"] [text "Meadow"]
    ]
  where
  links =
    [ Tuple "Tutorial" $ "https://github.com/input-output-hk/marlowe/blob/master/docs/tutorial-v2.0/README.md"
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

mainTabBar :: forall p. View -> HTML p (Query Unit)
mainTabBar activeView = navTabs_ (mkTab <$> tabs)
  where
  tabs =
    [ Editor /\ "Haskell Editor"
    , Simulation /\ "Simulation"
    ]

  mkTab (link /\ title) =
    navItem_
      [ a
          [ classes
              $ [ navLink
                ]
              <> activeClass
          , onClick $ const $ Just $ action $ ChangeView link
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

resultPane :: forall p. FrontendState -> HTML p (Query Unit)
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
                      , onClick $ input_ SendResult
                      , disabled (isLoading compilationResult || (not isSuccess) compilationResult)
                      ] [text "Send to Simulator"]
                  , code_
                      [ pre [class_ $ ClassName "success-code"] [text (unwrap result.result)]
                      ]
                  ]
              ]
          ]
      _ -> empty
