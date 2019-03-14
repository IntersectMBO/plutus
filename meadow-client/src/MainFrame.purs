module MainFrame (mainFrame) where

import API (SourceCode(SourceCode))
import Ace.Halogen.Component
  ( AceEffects
  , AceMessage
      ( TextChanged
      )
  , AceQuery
      ( GetEditor
      )
  )
import Ace.Types (ACE, Editor, Annotation)
import AjaxUtils (runAjaxTo)
import Analytics (Event, defaultEvent, trackEvent, ANALYTICS)
import Bootstrap
  ( active
  , btn
  , btnGroup
  , btnSmall
  , container
  , container_
  , hidden
  , navItem_
  , navLink
  , navTabs_
  , pullRight
  )
import Control.Monad.Aff.Class (class MonadAff, liftAff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Monad.Reader.Class (class MonadAsk)
import Data.Array as Array
import Data.Array (catMaybes, delete, snoc)
import Data.BigInteger (BigInteger, fromInt)
import Data.Either (Either(..))
import Data.Foldable (foldrDefault)
import Data.Function (flip)
import Data.Lens (assign, modifying, over, preview, set, use)
import Data.List (List(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))
import Data.Tuple.Nested ((/\))
import Editor (editorPane)
import FileEvents (FILE, preventDefault, readFileFromDragEvent)
import Gist (gistId)
import Gists (mkNewGist)
import Halogen (Component, action)
import Halogen.Component (ParentHTML)
import Halogen.ECharts (EChartsEffects)
import Halogen.HTML (ClassName(ClassName), HTML, a, div, div_, h1, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, href)
import Halogen.Query (HalogenM)
import Language.Haskell.Interpreter
  ( CompilationError
      ( CompilationError
      , RawError
      )
  )
import LocalStorage (LOCALSTORAGE)
import Meadow
  ( SPParams_
  , getOauthStatus
  , patchGistsByGistId
  , postGists
  , postContractHaskell
  )
import Network.HTTP.Affjax (AJAX)
import Network.RemoteData (RemoteData(Success, NotAsked), _Success)
import Data.Ord (min, max, (>=))
import Prelude
  ( type (~>)
  , Unit
  , Void
  , bind
  , const
  , discard
  , id
  , pure
  , show
  , unit
  , void
  , ($)
  , (+)
  , (-)
  , (<$>)
  , (<<<)
  , (<>)
  , (==)
  )
import Semantics
  ( BlockNumber
  , Choice
  , Contract(..)
  , WIdChoice(..)
  , IdChoice(..)
  , IdInput(..)
  , IdOracle
  , ErrorResult(..) 
  , MApplicationResult(..)
  , Person
  , State(..)
  , applyTransaction
  , collectNeededInputsFromContract
  , emptyState
  , peopleFromStateAndContract
  , readContract
  , reduce
  , scoutPrimitives
  )
import Servant.PureScript.Settings (SPSettings_)
import Simulation (simulationPane)
import StaticData (bufferLocalStorageKey, marloweBufferLocalStorageKey)
import Text.Parsing.Simple (parse)
import Types
  ( ChildQuery
  , ChildSlot
  , EditorSlot(..)
  , FrontendState
  , InputData
  , MarloweEditorSlot(..)
  , MarloweError(..)
  , MarloweState
  , OracleEntry
  , Query(..)
  , TransactionData
  , View(..)
  , _authStatus
  , _blockNum
  , _choiceData
  , _contract
  , _createGistResult
  , _marloweCompileResult
  , _marloweState
  , _input
  , _inputs
  , _oracleData
  , _runResult
  , _signatures
  , _transaction
  , _view
  , cpEditor
  , cpMarloweEditor
  )

import Ace.EditSession as Session
import Ace.Editor as Editor
import Data.String as String
import Halogen as H
import LocalStorage as LocalStorage
import Marlowe.Parser as Parser
import StaticData as StaticData

emptyInputData :: InputData
emptyInputData = { inputs: Map.empty
                 , choiceData: Map.empty
                 , oracleData: Map.empty }

emptyTransactionData :: TransactionData
emptyTransactionData = { inputs: []
                       , signatures: Map.empty
                       , outcomes: Map.empty
                       }

emptyMarloweState :: MarloweState
emptyMarloweState = { input: emptyInputData
                    , transaction: emptyTransactionData
                    , state: emptyState
                    , blockNum: (fromInt 0)
                    , moneyInContract: (fromInt 0)
                    , contract: Null
                    }

initialState :: FrontendState
initialState = { view: Editor
               , runResult: NotAsked
               , marloweCompileResult: Right unit
               , authStatus: NotAsked
               , createGistResult: NotAsked
               , marloweState: emptyMarloweState
               }

------------------------------------------------------------
mainFrame ::
  forall m aff.
  MonadAff (EChartsEffects (AceEffects (localStorage :: LOCALSTORAGE, file :: FILE, ajax :: AJAX, analytics :: ANALYTICS | aff))) m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  Component HTML Query Unit Void m
mainFrame = H.lifecycleParentComponent { initialState: const initialState
                                       , render
                                       , eval: evalWithAnalyticsTracking
                                       , receiver: const Nothing
                                       , initializer: Just $ H.action $ CheckAuthStatus
                                       , finalizer: Nothing
                                       }

evalWithAnalyticsTracking ::
  forall m aff.
  MonadAff (localStorage :: LOCALSTORAGE, file :: FILE, ace :: ACE, ajax :: AJAX, analytics :: ANALYTICS | aff) m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  Query
    ~> HalogenM FrontendState Query ChildQuery ChildSlot Void m
evalWithAnalyticsTracking query = do
  liftEff $ analyticsTracking query
  evalF query

analyticsTracking ::
  forall eff a.
  Query a ->
  Eff (analytics :: ANALYTICS | eff) Unit
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

toEvent (PublishGist _) = Just $ (defaultEvent "Publish") { label = Just "Gist" }

toEvent (ChangeView view _) = Just $ (defaultEvent "View") { label = Just $ show view }

toEvent (LoadScript script a) = Just $ (defaultEvent "LoadScript") { label = Just script }

toEvent (LoadMarloweScript script a) = Just $ (defaultEvent "LoadMarloweScript") { label = Just script }

toEvent (CompileProgram a) = Just $ defaultEvent "CompileProgram"

toEvent (ScrollTo _ _) = Nothing

toEvent (SetSignature _ _) = Nothing

toEvent (ApplyTrasaction _) = Just $ defaultEvent "ApplyTransaction"

toEvent (NextBlock _) = Just $ defaultEvent "NextBlock"

toEvent (AddAnyInput _ _) = Nothing

toEvent (RemoveAnyInput _ _) = Nothing

toEvent (SetChoice _ _) = Nothing

toEvent (SetOracleVal _ _) = Nothing

toEvent (SetOracleBn _ _) = Nothing

toEvent (CompileMarlowe _) = Just $ defaultEvent "CompileMarlowe"

saveBuffer ::
  forall eff.
  String ->
  Eff (localStorage :: LOCALSTORAGE | eff) Unit
saveBuffer text = LocalStorage.setItem bufferLocalStorageKey text

saveMarloweBuffer ::
  forall eff.
  String ->
  Eff (localStorage :: LOCALSTORAGE | eff) Unit
saveMarloweBuffer text = LocalStorage.setItem marloweBufferLocalStorageKey text

resizeSigsAux ::
  Map Person Boolean ->
  Map Person Boolean ->
  List Person ->
  Map Person Boolean
resizeSigsAux ma ma2 Nil = ma2

resizeSigsAux ma ma2 (Cons x y) = case Map.lookup x ma of
  Just z -> resizeSigsAux ma (Map.insert x z ma2) y
  Nothing -> resizeSigsAux ma (Map.insert x false ma2) y

resizeSigs :: List Person -> Map Person Boolean -> Map Person Boolean
resizeSigs li ma = resizeSigsAux ma Map.empty li

updateSignatures :: MarloweState -> MarloweState
updateSignatures oldState =
  over (_transaction <<< _signatures) (resizeSigs (peopleFromStateAndContract (oldState.state) (oldState.contract))) oldState

updateChoices :: State -> Set IdInput -> Map Person (Map BigInteger Choice)
                 -> Map Person (Map BigInteger Choice)
updateChoices (State state) inputs cmap =
  foldrDefault addChoice Map.empty inputs
  where
    addChoice (InputIdChoice (IdChoice {choice: idChoice, person})) a =
      let pmap = case Map.lookup person a of
                   Nothing -> Map.empty
                   Just y -> y in
      let dval = case Map.lookup person cmap of
                    Nothing -> fromInt 0
                    Just z -> case Map.lookup idChoice z of
                                Nothing -> fromInt 0
                                Just v -> v in
      if Map.member (WIdChoice (IdChoice {choice: idChoice, person})) state.choices
      then a 
      else Map.insert person (Map.insert idChoice dval pmap) a
    addChoice _ a = a

updateOracles :: BlockNumber -> State -> Set IdInput -> Map IdOracle OracleEntry -> Map IdOracle OracleEntry
updateOracles cbn (State state) inputs omap =
  foldrDefault addOracle Map.empty inputs
  where
    addOracle (IdOracle idOracle) a =
        case Map.lookup idOracle omap, Map.lookup idOracle state.oracles of
             Nothing, Nothing -> Map.insert idOracle {blockNumber: cbn, value: fromInt 0} a
             Just {blockNumber: bn, value}, Just {blockNumber: lbn} ->
               if (lbn >= cbn)
               then a
               else Map.insert idOracle {blockNumber: max (lbn + fromInt 1) bn, value} a
             Just {blockNumber, value}, Nothing ->
               Map.insert idOracle {blockNumber: min blockNumber cbn, value} a
             Nothing, Just {blockNumber, value} ->
               if (blockNumber >= cbn)
               then a
               else Map.insert idOracle {blockNumber: cbn, value} a
    addOracle _ a = a

updateActions :: MarloweState -> {state :: State, contract :: Contract} -> MarloweState
updateActions oldState {state, contract} =
  set (_input <<< _inputs) (scoutPrimitives oldState.blockNum state contract)
  (over (_input <<< _choiceData) (updateChoices state neededInputs)
  (over (_input <<< _oracleData) (updateOracles oldState.blockNum state neededInputs)
   oldState))
  where
    neededInputs = collectNeededInputsFromContract contract

simulateState :: MarloweState -> {state :: State, contract :: Contract}
simulateState state =
  case applyTransaction inps sigs bn st c mic of
    MSuccessfullyApplied {state: newState, contract: newContract} _ ->
            {state: newState, contract: newContract}
    MCouldNotApply InvalidInput ->
	    if inps == Nil
	    then {state: st, contract: reduce state.blockNum state.state c}
	    else {state: emptyState, contract: Null}
    MCouldNotApply _ -> {state: emptyState, contract: Null}
  where
    inps = Array.toUnfoldable (state.transaction.inputs)
    sigs = Set.fromFoldable (Map.keys (Map.filter id (state.transaction.signatures)))
    bn = state.blockNum
    st = state.state
    c = state.contract
    mic = state.moneyInContract

updateState :: MarloweState -> MarloweState
updateState oldState = actState
  where
    sigState = updateSignatures oldState
    actState = updateActions sigState (simulateState sigState)

updateContractInState :: String -> MarloweState -> MarloweState
updateContractInState text state = updateState newState 
  where
    con = case readContract text of
            Just pcon -> pcon
            Nothing -> Null
    newState = set (_contract) con state

evalF ::
  forall m aff.
  MonadAff (localStorage :: LOCALSTORAGE, file :: FILE, ace :: ACE, ajax :: AJAX | aff) m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  Query
    ~> HalogenM FrontendState Query ChildQuery ChildSlot Void m
evalF (HandleEditorMessage (TextChanged text) next) = do
  liftEff $ saveBuffer text
  pure next

evalF (HandleDragEvent event next) = do
  liftEff $ preventDefault event
  pure next

evalF (HandleDropEvent event next) = do
  liftEff $ preventDefault event
  contents <- liftAff $ readFileFromDragEvent event
  void $ withEditor $ Editor.setValue contents (Just 1)
  pure next

evalF (MarloweHandleEditorMessage (TextChanged text) next) = do
  liftEff $ saveMarloweBuffer text
  modifying (_marloweState) (updateContractInState text)
  pure next

evalF (MarloweHandleDragEvent event next) = do
  liftEff $ preventDefault event
  pure next

evalF (MarloweHandleDropEvent event next) = do
  liftEff $ preventDefault event
  contents <- liftAff $ readFileFromDragEvent event
  void $ withMarloweEditor $ Editor.setValue contents (Just 1)
  pure next

evalF (CheckAuthStatus next) = do
  authResult <- runAjaxTo _authStatus getOauthStatus
  pure next

evalF (PublishGist next) = do
  mContents <- withEditor Editor.getValue
  case mkNewGist mContents of
    Nothing -> pure next
    Just newGist -> do
      mGist <- use _createGistResult
      let apiCall = case preview (_Success <<< gistId) mGist of
            Nothing -> postGists newGist
            Just gistId -> patchGistsByGistId newGist gistId
      void $ runAjaxTo _createGistResult apiCall
      pure next

evalF (ChangeView view next) = do
  assign _view view
  pure next

evalF (LoadScript key next) = do
  case Map.lookup key StaticData.demoFiles of
    Nothing -> pure next
    Just contents -> do
      void $ withEditor $ Editor.setValue contents (Just 1)
      assign _runResult NotAsked
      pure next

evalF (LoadMarloweScript key next) = do
  case Map.lookup key StaticData.marloweContracts of
    Nothing -> pure next
    Just contents -> do
      void $ withMarloweEditor $ Editor.setValue contents (Just 1)
      pure next

evalF (CompileProgram next) = do
  mContents <- withEditor Editor.getValue
  case mContents of
    Nothing -> pure next
    Just contents -> do
      result <- runAjaxTo _runResult $ postContractHaskell $ SourceCode contents
      -- Update the error display.
      -- Update the error display.
      -- Update the error display.
      -- Update the error display.
      void $ withEditor $ showCompilationErrorAnnotations $ case result of
        Success (Left errors) -> errors
        _ -> []
      pure next

evalF (ScrollTo { row, column } next) = do
  void $ withEditor $ Editor.gotoLine row (Just column) (Just true)
  pure next

evalF (SetSignature { person, isChecked } next) = do
  modifying (_marloweState <<< _transaction <<< _signatures) (Map.insert person isChecked)
  modifying (_marloweState) updateState
  pure next

--evalF (UpdatePerson person next) = do
--  pure next
-- updating a person will require running the simulation so that the next suggested actions can be added
-- although I'm not sure from the design what are suggested and what are manual
-- updating a person will require running the simulation so that the next suggested actions can be added
-- although I'm not sure from the design what are suggested and what are manual
-- updating a person will require running the simulation so that the next suggested actions can be added
-- although I'm not sure from the design what are suggested and what are manual
--  currentState <- use _marloweState
--  assign (_marloweState <<< _people) $ Map.update (const <<< Just $ person) person.id currentState.people
evalF (ApplyTrasaction next) = pure next

evalF (NextBlock next) = do
  modifying (_marloweState <<< _blockNum) (\x ->
    x + ((fromInt 1) :: BigInteger))
  modifying (_marloweState) updateState
  pure next

evalF (AddAnyInput {person, anyInput} next) = do
  modifying (_marloweState <<< _transaction <<< _inputs) ((flip snoc) anyInput)
  case person of
    Just per -> do modifying (_marloweState <<< _transaction <<< _signatures)
                             (Map.insert per true)
                   modifying (_marloweState) updateState
                   pure next
    Nothing -> do modifying (_marloweState) updateState
                  pure next

evalF (RemoveAnyInput anyInput next) = do
  modifying (_marloweState <<< _transaction <<< _inputs) (delete anyInput)
  modifying (_marloweState) updateState
  pure next

evalF (SetChoice {idChoice: (IdChoice {choice, person}), value} next) = do
  modifying (_marloweState <<< _input <<< _choiceData)
    (Map.update (Just <<< (Map.update (const $ Just value) choice)) person)
  modifying (_marloweState) updateState
  pure next

evalF (SetOracleVal {idOracle, value} next) = do
  modifying (_marloweState <<< _input <<< _oracleData)
    (Map.update (\x -> Just (x {value = value})) idOracle)
  modifying (_marloweState) updateState
  pure next

evalF (SetOracleBn {idOracle, blockNumber} next) = do
  modifying (_marloweState <<< _input <<< _oracleData)
    (Map.update (\x -> Just (x {blockNumber = blockNumber})) idOracle)
  modifying (_marloweState) updateState
  pure next

evalF (CompileMarlowe next) = do
  mContents <- withMarloweEditor Editor.getValue
  case mContents of
    Nothing -> pure next
    Just contents -> do
      let contract = parse Parser.contract contents
      case contract of
        Right c -> do
          assign _marloweCompileResult $ Left [MarloweError "oh no"]
          pure next
        Left err -> do
          assign _marloweCompileResult $ Left [MarloweError err]
          pure next

------------------------------------------------------------
-- | Handles the messy business of running an editor command if the
-- editor is up and running.
withEditor ::
  forall m eff a.
  MonadEff (ace :: ACE | eff) m =>
  (Editor -> Eff (ace :: ACE | eff) a) ->
  HalogenM FrontendState Query ChildQuery ChildSlot Void m (Maybe a)
withEditor action = do
  mEditor <- H.query' cpEditor EditorSlot $ H.request GetEditor
  case mEditor of
    Just (Just editor) -> do
      liftEff $ Just <$> action editor
    _ -> pure Nothing

withMarloweEditor ::
  forall m eff a.
  MonadEff (ace :: ACE | eff) m =>
  (Editor -> Eff (ace :: ACE | eff) a) ->
  HalogenM FrontendState Query ChildQuery ChildSlot Void m (Maybe a)
withMarloweEditor action = do
  mEditor <- H.query' cpMarloweEditor MarloweEditorSlot $ H.request GetEditor
  case mEditor of
    Just (Just editor) -> do
      liftEff $ Just <$> action editor
    _ -> pure Nothing

showCompilationErrorAnnotations ::
  forall m.
  Array CompilationError ->
  Editor ->
  Eff (ace :: ACE | m) Unit
showCompilationErrorAnnotations errors editor = do
  session <- Editor.getSession editor
  Session.setAnnotations (catMaybes (toAnnotation <$> errors)) session

toAnnotation :: CompilationError -> Maybe Annotation
toAnnotation (RawError _) = Nothing

toAnnotation (CompilationError { row, column, text }) = Just { "type": "error"
                                                             , row: row - 1
                                                             , column
                                                             , text: String.joinWith "\n" text
                                                             }

render ::
  forall m aff.
  MonadAff (EChartsEffects (AceEffects (localStorage :: LOCALSTORAGE | aff))) m =>
  FrontendState ->
  ParentHTML Query ChildQuery ChildSlot m
render state = div [ class_ $ ClassName "main-frame"
                   ] [ container_ [ mainHeader
                                  , mainTabBar state.view
                                  ]
                     , viewContainer state.view Editor $ [editorPane state]
                     , viewContainer state.view Simulation $ [ simulationPane state
                                                             ]
                     ]

viewContainer :: forall p i. View -> View -> Array (HTML p i) -> HTML p i
viewContainer currentView targetView = if currentView == targetView
  then div [classes [container]]
  else div [classes [container, hidden]]

mainHeader :: forall p. HTML p (Query Unit)
mainHeader = div_ [ div [classes [btnGroup, pullRight]] (makeLink <$> links)
                  , h1 [class_ $ ClassName "main-title"] [text "Meadow"]
                  ]
  where
  links = [ Tuple "Getting Started" "https://testnet.iohkdev.io/plutus/get-started/writing-contracts-in-plutus/"
          , Tuple "Tutorial" "https://github.com/input-output-hk/plutus/blob/master/plutus-tutorial/tutorial/Tutorial/02-wallet-api.md"
          , Tuple "API" "https://input-output-hk.github.io/plutus/"
          , Tuple "Privacy" "https://static.iohk.io/docs/data-protection/iohk-data-protection-gdpr-policy.pdf"
          ]
  makeLink (Tuple name link) = a [ classes [ btn
                                           , btnSmall
                                           ]
                                 , href link
                                 ] [ text name
                                   ]

mainTabBar :: forall p. View -> HTML p (Query Unit)
mainTabBar activeView = navTabs_ (mkTab <$> tabs)
  where
  tabs = [ Editor /\ "Haskell Editor"
         , Simulation /\ "Simulation"
         ]
  mkTab (link /\ title) = navItem_ [ a [ classes $ [ navLink
                                                   ] <> activeClass
                                       , onClick $ const $ Just $ action $ ChangeView link
                                       ] [ text title
                                         ]
                                   ]
    where
    activeClass = if link == activeView
      then [ active
           ]
      else []
