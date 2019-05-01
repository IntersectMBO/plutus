module MainFrame (mainFrame) where

import API (_RunResult)
import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceMessage(TextChanged), AceQuery(GetEditor))
import Ace.Types (Editor, Annotation)
import AjaxUtils (runAjaxTo)
import Analytics (Event, defaultEvent, trackEvent)
import Bootstrap (active, btn, btnGroup, btnInfo, btnPrimary, btnSmall, col_, container, container_, empty, hidden, listGroupItem_, listGroup_, navItem_, navLink, navTabs_, noGutters, pullRight, row)
import Control.Monad.Reader.Class (class MonadAsk)
import Control.Monad.State.Trans (class MonadState)
import Data.Array (catMaybes, delete, snoc)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.Either (Either(..))
import Data.Foldable (foldrDefault)
import Data.Function (flip)
import Data.Functor.Coproduct (Coproduct)
import Data.Lens (assign, modifying, over, preview, set, use, view)
import Data.List (List(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing))
import Data.Newtype (unwrap)
import Data.Ord (min, max, (>=))
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.Tuple (Tuple(Tuple))
import Data.Tuple.Nested ((/\))
import Editor (editorPane)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import FileEvents (preventDefault, readFileFromDragEvent)
import Gist (gistId)
import Gists (mkNewGist)
import Halogen (Component, action)
import Halogen as H
import Halogen.Component (ParentHTML)
import Halogen.HTML (ClassName(ClassName), HTML, a, button, code_, div, div_, h1, pre, strong_, text)
import Halogen.HTML.Events (onClick, input_)
import Halogen.HTML.Properties (class_, classes, href, disabled)
import Halogen.Query (HalogenM)
import Language.Haskell.Interpreter (SourceCode(SourceCode), InterpreterError(CompilationErrors, TimeoutError), CompilationError(CompilationError, RawError), InterpreterResult(InterpreterResult), _InterpreterResult)
import LocalStorage as LocalStorage
import Marlowe.Parser (contract)
import Marlowe.Pretty (pretty)
import Marlowe.Semantics (ErrorResult(InvalidInput), IdInput(IdOracle, InputIdChoice), MApplicationResult(MCouldNotApply, MSuccessfullyApplied), OracleDataPoint(..), State(State), TransactionOutcomes, applyTransaction, collectNeededInputs, emptyState, peopleFromStateAndContract, reduce, scoutPrimitives)
import Marlowe.Types (BlockNumber, Choice, Contract(Null), IdChoice(IdChoice), IdOracle, Person, WIdChoice(WIdChoice))
import Meadow (SPParams_, getOauthStatus, patchGistsByGistId, postGists, postContractHaskell)
import Network.RemoteData (RemoteData(Success, NotAsked), _Success, isLoading, isSuccess)
import Prelude (add, one, zero, not, (||), type (~>), Unit, Void, bind, const, discard, identity, pure, show, unit, void, (#), ($), (+), (-), (<$>), (<<<), (<>), (==))
import Servant.PureScript.Settings (SPSettings_)
import Simulation (simulationPane)
import StaticData (bufferLocalStorageKey, marloweBufferLocalStorageKey)
import StaticData as StaticData
import Text.Parsing.Parser (runParser)
import Types (ChildQuery, ChildSlot, EditorSlot(EditorSlot), FrontendState, InputData, MarloweEditorSlot(MarloweEditorSlot), MarloweState, OracleEntry, Query(ChangeView, ResetSimulator, SetOracleBn, SetOracleVal, SetChoice, RemoveAnyInput, AddAnyInput, NextBlock, ApplyTransaction, SetSignature, ScrollTo, CompileProgram, LoadMarloweScript, LoadScript, PublishGist, SendResult, CheckAuthStatus, MarloweHandleDropEvent, MarloweHandleDragEvent, MarloweHandleEditorMessage, HandleDropEvent, HandleDragEvent, HandleEditorMessage), TransactionData, TransactionValidity(..), View(Simulation, Editor), _authStatus, _blockNum, _choiceData, _contract, _createGistResult, _input, _inputs, _marloweState, _moneyInContract, _oldContract, _oracleData, _outcomes, _compilationResult, _signatures, _state, _transaction, _validity, _view, cpEditor, cpMarloweEditor, _result)

emptyInputData :: InputData
emptyInputData = { inputs: Map.empty
                 , choiceData: Map.empty
                 , oracleData: Map.empty }

emptyTransactionData :: TransactionData
emptyTransactionData = { inputs: []
                       , signatures: Map.empty
                       , outcomes: Map.empty
                       , validity: EmptyTransaction
                       }

emptyMarloweState :: MarloweState
emptyMarloweState = { input: emptyInputData
                    , transaction: emptyTransactionData
                    , state: emptyState
                    , blockNum: zero
                    , moneyInContract: zero
                    , contract: Nothing
                    }

initialState :: FrontendState
initialState = { view: Editor
               , compilationResult: NotAsked
               , marloweCompileResult: Right unit
               , authStatus: NotAsked
               , createGistResult: NotAsked
               , marloweState: emptyMarloweState
               , oldContract: Nothing
               }

------------------------------------------------------------
mainFrame ::
  forall m.
  MonadAff m =>
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
  forall m.
  MonadAff m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  Query
    ~> HalogenM FrontendState Query ChildQuery ChildSlot Void m
evalWithAnalyticsTracking query = do
  liftEffect $ analyticsTracking query
  evalF query

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

toEvent (PublishGist _) = Just $ (defaultEvent "Publish") { label = Just "Gist" }

toEvent (ChangeView view _) = Just $ (defaultEvent "View") { label = Just $ show view }

toEvent (LoadScript script a) = Just $ (defaultEvent "LoadScript") { label = Just script }

toEvent (LoadMarloweScript script a) = Just $ (defaultEvent "LoadMarloweScript") { label = Just script }

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

saveBuffer ::
  String ->
  Effect Unit
saveBuffer text = LocalStorage.setItem bufferLocalStorageKey text

saveMarloweBuffer ::
  String ->
  Effect Unit
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
  case oldState.contract of
    Just oldContract -> over (_transaction <<< _signatures) (resizeSigs (peopleFromStateAndContract (oldState.state) oldContract)) oldState
    Nothing -> oldState

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
                    Nothing -> zero
                    Just z -> case Map.lookup idChoice z of
                                Nothing -> zero
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
             Nothing, Nothing -> Map.insert idOracle {blockNumber: cbn, value: zero} a
             Just {blockNumber: bn, value}, Just (OracleDataPoint {blockNumber: lbn}) ->
               if (lbn >= cbn)
               then a
               else Map.insert idOracle {blockNumber: max (lbn + one) bn, value} a
             Just {blockNumber, value}, Nothing ->
               Map.insert idOracle {blockNumber: min blockNumber cbn, value} a
             Nothing, Just (OracleDataPoint {blockNumber, value}) ->
               if (blockNumber >= cbn)
               then a
               else Map.insert idOracle {blockNumber: cbn, value} a
    addOracle _ a = a

updateActions :: MarloweState -> {state :: State, contract :: Contract, outcome :: TransactionOutcomes, validity :: TransactionValidity} -> MarloweState
updateActions oldState {state, contract, outcome, validity}
  = set (_transaction <<< _validity) validity oldState
  # set (_transaction <<< _outcomes) outcome
  # over (_input <<< _oracleData) (updateOracles oldState.blockNum state neededInputs)
  # over (_input <<< _choiceData) (updateChoices state neededInputs)
  # set (_input <<< _inputs) (scoutPrimitives oldState.blockNum state contract)
  where
    neededInputs = collectNeededInputs contract

simulateState :: MarloweState -> Maybe {state :: State, contract :: Contract, outcome :: TransactionOutcomes, validity :: TransactionValidity}
simulateState state =
  case state.contract of
    Just c -> Just (case applyTransaction inps sigs bn st c mic of
                      MSuccessfullyApplied {state: newState, contract: newContract, outcome: outcome} inputWarnings ->
                              {state: newState, contract: newContract,
                               outcome: outcome, validity: ValidTransaction inputWarnings}
                      MCouldNotApply InvalidInput ->
                              if (inps == Nil)
                              then {state: st, contract: reduce state.blockNum state.state c,
                                    outcome: Map.empty, validity: EmptyTransaction}
                              else {state: emptyState, contract: Null,
                                    outcome: Map.empty, validity: InvalidTransaction InvalidInput}
                      MCouldNotApply err -> {state: emptyState, contract: Null,
                                             outcome: Map.empty, validity: InvalidTransaction err})
    Nothing -> Nothing
  where
    inps = Array.toUnfoldable (state.transaction.inputs)
    sigs = Set.fromFoldable (Map.keys (Map.filter identity (state.transaction.signatures)))
    bn = state.blockNum
    st = state.state
    mic = state.moneyInContract

applyTransactionM :: MarloweState -> MarloweState
applyTransactionM oldState =
  case oldState.contract of
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

updateStateP :: MarloweState -> MarloweState
updateStateP oldState = actState
  where
    sigState = updateSignatures oldState
    mSimulatedState = simulateState sigState
    actState = case mSimulatedState of
                 Just simulatedState -> updateActions sigState simulatedState
                 Nothing -> sigState

updateState ::
  forall m.
  MonadEffect m
  => HalogenM FrontendState Query (Coproduct AceQuery AceQuery) (Either EditorSlot MarloweEditorSlot) Void m Unit
updateState = do
  saveInitialState
  modifying (_marloweState) (updateStateP)

updateContractInStateP :: String -> MarloweState -> MarloweState
updateContractInStateP text state = set (_contract) con state
  where
    con = case runParser text contract of
            Right pcon -> Just pcon
            Left _ -> Nothing

updateContractInState :: forall m. MonadState FrontendState m => String -> m Unit
updateContractInState text = do
   modifying (_marloweState) (updateContractInStateP text)
   modifying (_marloweState) (updateStateP)

saveInitialState ::
  forall m.
  MonadEffect m
  => HalogenM FrontendState Query (Coproduct AceQuery AceQuery) (Either EditorSlot MarloweEditorSlot) Void m Unit
saveInitialState = do
  oldContract <- withMarloweEditor Editor.getValue
  modifying (_oldContract) (\x -> case x of
                                    Nothing -> Just (case oldContract of
                                                      Nothing -> ""
                                                      Just y -> y)
                                    _ -> x)

resetContract :: 
  forall m.
  MonadEffect m
  => HalogenM FrontendState Query (Coproduct AceQuery AceQuery) (Either EditorSlot MarloweEditorSlot) Void m Unit
resetContract = do
  newContract <- withMarloweEditor Editor.getValue
  modifying (_marloweState) (const emptyMarloweState)
  modifying (_oldContract) (const Nothing)
  updateContractInState (case newContract of
                           Nothing -> ""
                           Just x -> x)


evalF ::
  forall m.
  MonadAff m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  Query
    ~> HalogenM FrontendState Query ChildQuery ChildSlot Void m
evalF (HandleEditorMessage (TextChanged text) next) = do
  liftEffect $ saveBuffer text
  pure next

evalF (HandleDragEvent event next) = do
  liftEffect $ preventDefault event
  pure next

evalF (HandleDropEvent event next) = do
  liftEffect $ preventDefault event
  contents <- liftAff $ readFileFromDragEvent event
  void $ withEditor $ Editor.setValue contents (Just 1)
  pure next

evalF (MarloweHandleEditorMessage (TextChanged text) next) = do
  liftEffect $ saveMarloweBuffer text
  updateContractInState text
  pure next

evalF (MarloweHandleDragEvent event next) = do
  liftEffect $ preventDefault event
  pure next

evalF (MarloweHandleDropEvent event next) = do
  liftEffect $ preventDefault event
  contents <- liftAff $ readFileFromDragEvent event
  void $ withMarloweEditor $ Editor.setValue contents (Just 1)
  updateContractInState contents
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
      pure next

evalF (LoadMarloweScript key next) = do
  case Map.lookup key StaticData.marloweContracts of
    Nothing -> pure next
    Just contents -> do
      void $ withMarloweEditor $ Editor.setValue contents (Just 1)
      updateContractInState contents
      resetContract
      pure next

evalF (CompileProgram next) = do
  mContents <- withEditor Editor.getValue
  case mContents of
    Nothing -> pure next
    Just contents -> do
      result <- runAjaxTo _compilationResult $ unwrap <$> (postContractHaskell $ SourceCode contents)
      -- Update the error display.
      -- Update the error display.
      -- Update the error display.
      -- Update the error display.
      void $ withEditor $ showCompilationErrorAnnotations $ case result of
        Success (Left errors) -> toAnnotations errors
        _ -> []
      pure next

evalF (SendResult next) = do
  mContract <- use (_compilationResult)
  let contract = case mContract of
                   Success (Right x) -> view (_InterpreterResult <<< _result <<< _RunResult) x
                   _ -> ""
  void $ withMarloweEditor $ Editor.setValue contract (Just 1)
  updateContractInState contract
  resetContract
  assign _view (Simulation)
  pure next


evalF (ScrollTo { row, column } next) = do
  void $ withEditor $ Editor.gotoLine row (Just column) (Just true)
  pure next

evalF (SetSignature { person, isChecked } next) = do
  modifying (_marloweState <<< _transaction <<< _signatures) (Map.insert person isChecked)
  updateState
  pure next

evalF (ApplyTransaction next) = do
  saveInitialState
  modifying (_marloweState) applyTransactionM
  mCurrContract <- use (_marloweState <<< _contract)
  case mCurrContract of
   Just currContract -> do void $ withMarloweEditor $ Editor.setValue (show $ pretty currContract) (Just 1)
                           updateState
                           pure next
   Nothing -> pure next

evalF (NextBlock next) = do
  modifying (_marloweState <<< _blockNum) (add one)
  updateState
  pure next

evalF (AddAnyInput {person, anyInput} next) = do
  modifying (_marloweState <<< _transaction <<< _inputs) ((flip snoc) anyInput)
  case person of
    Just per -> do modifying (_marloweState <<< _transaction <<< _signatures)
                             (Map.insert per true)
                   updateState
                   pure next
    Nothing -> do updateState
                  pure next

evalF (RemoveAnyInput anyInput next) = do
  modifying (_marloweState <<< _transaction <<< _inputs) (delete anyInput)
  updateState
  pure next

evalF (SetChoice {idChoice: (IdChoice {choice, person}), value} next) = do
  modifying (_marloweState <<< _input <<< _choiceData)
    (Map.update (Just <<< (Map.update (const $ Just value) choice)) person)
  updateState
  pure next

evalF (SetOracleVal {idOracle, value} next) = do
  modifying (_marloweState <<< _input <<< _oracleData)
    (Map.update (\x -> Just (x {value = value})) idOracle)
  updateState
  pure next

evalF (SetOracleBn {idOracle, blockNumber} next) = do
  modifying (_marloweState <<< _input <<< _oracleData)
    (Map.update (\x -> Just (x {blockNumber = blockNumber})) idOracle)
  updateState
  pure next

evalF (ResetSimulator next) = do
  oldContract <- use (_oldContract)
  currContract <- withMarloweEditor Editor.getValue
  let newContract = case oldContract of
                      Just x -> x
                      Nothing -> case currContract of
                                   Nothing -> ""
                                   Just y -> y
  void $ withMarloweEditor $ Editor.setValue newContract (Just 1)
  resetContract
  pure next
--  mContents <- withMarloweEditor Editor.getValue
--  case mContents of
--    Nothing -> pure next
--    Just contents -> do
--      let contract = parse Parser.contract contents
--      case contract of
--        Right c -> do
--          assign _marloweCompileResult $ Left [MarloweError "oh no"]
--          pure next
--        Left err -> do
--          assign _marloweCompileResult $ Left [MarloweError err]
--          pure next

------------------------------------------------------------
-- | Handles the messy business of running an editor command if the
-- editor is up and running.
withEditor ::
  forall m a.
  MonadEffect m =>
  (Editor -> Effect a) ->
  HalogenM FrontendState Query ChildQuery ChildSlot Void m (Maybe a)
withEditor action = do
  mEditor <- H.query' cpEditor EditorSlot $ H.request GetEditor
  case mEditor of
    Just (Just editor) -> do
      liftEffect $ Just <$> action editor
    _ -> pure Nothing

withMarloweEditor ::
  forall m a.
  MonadEffect m =>
  (Editor -> Effect a) ->
  HalogenM FrontendState Query ChildQuery ChildSlot Void m (Maybe a)
withMarloweEditor action = do
  mEditor <- H.query' cpMarloweEditor MarloweEditorSlot $ H.request GetEditor
  case mEditor of
    Just (Just editor) -> do
      liftEffect $ Just <$> action editor
    _ -> pure Nothing

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

toAnnotation (CompilationError { row, column, text }) = Just { "type": "error"
                                                             , row: row - 1
                                                             , column
                                                             , text: String.joinWith "\n" text
                                                             }

render ::
  forall m.
  MonadAff m =>
  FrontendState ->
  ParentHTML Query ChildQuery ChildSlot m
render state = div [ class_ $ ClassName "main-frame" ]
                   [ container_ [ mainHeader
                                , div [ classes [ row, noGutters ] ]
                                      [ col_ [ mainTabBar state.view ]
                                      ]
                                ]
                   , viewContainer state.view Editor $ [ loadScriptsPane
                                                       , editorPane defaultContents state.compilationResult
                                                       , resultPane state
                                                       ]
                   , viewContainer state.view Simulation $ [ simulationPane state
                                                           ]
                   ]
    where
      defaultContents = Map.lookup "Escrow" StaticData.demoFiles

loadScriptsPane :: forall p. HTML p (Query Unit)
loadScriptsPane = div [class_ $ ClassName "mb-3"]
                      (Array.cons (strong_ [ text "Demos: "
                                            ]) (loadScriptButton <$> Array.fromFoldable (Map.keys StaticData.demoFiles)))

loadScriptButton :: forall p. String -> HTML p (Query Unit)
loadScriptButton key = button [ classes [btn, btnInfo, btnSmall]
                              , onClick $ input_ $ LoadScript key
                              ] [text key]

viewContainer :: forall p i. View -> View -> Array (HTML p i) -> HTML p i
viewContainer currentView targetView = if currentView == targetView
  then div [classes [container]]
  else div [classes [container, hidden]]

mainHeader :: forall p. HTML p (Query Unit)
mainHeader = div_ [ div [classes [btnGroup, pullRight]] (makeLink <$> links)
                  , h1 [class_ $ ClassName "main-title"] [text "Meadow"]
                  ]
  where
  links = [ Tuple "Tutorial" $ "https://github.com/input-output-hk/marlowe/blob/master/docs/tutorial-v2.0/README.md"
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

resultPane :: forall p. FrontendState -> HTML p (Query Unit)
resultPane state = case state.compilationResult of
    Success (Right (InterpreterResult result)) ->
      listGroup_
        [ listGroupItem_
          [ div_
            [ button [ classes [ btn
                                   , btnPrimary
                                   , ClassName "float-right"
                                   ]
                         , onClick $ input_ SendResult
                         , disabled ((isLoading state.compilationResult) || ((not isSuccess) state.compilationResult))
                         ] [ text "Send to Simulator" ]
            , code_
              [ pre
                [class_ $ ClassName "success-code"]
                [ text (unwrap result.result) ]
              ]
            ]
          ]
        ]
    _ -> empty
