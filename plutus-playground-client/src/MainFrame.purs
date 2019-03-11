module MainFrame
  ( mainFrame
  ) where

import Types

import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceEffects, AceMessage(TextChanged), AceQuery(GetEditor))
import Ace.Types (ACE, Editor, Annotation)
import Action (simulationPane)
import AjaxUtils (ajaxErrorPane, runAjaxTo)
import Analytics (Event, defaultEvent, trackEvent, ANALYTICS)
import Bootstrap (active, btn, btnGroup, btnSmall, container, container_, hidden, navItem_, navLink, navTabs_, pullRight)
import Chain (mockchainChartOptions, balancesChartOptions, evaluationPane)
import Control.Comonad (extract)
import Control.Monad.Aff.Class (class MonadAff, liftAff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Reader.Class (class MonadAsk)
import Control.Monad.State (class MonadState)
import Control.Monad.Trans.Class (lift)
import Data.Array (catMaybes, (..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic (gEq)
import Data.Lens (_1, _2, _Just, _Right, assign, maximumOf, modifying, over, preview, set, traversed, use, view)
import Data.Lens.Index (ix)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(Tuple))
import Data.Tuple.Nested ((/\))
import ECharts.Monad (interpret)
import Editor (editorPane)
import FileEvents (FILE, preventDefault, readFileFromDragEvent)
import Gist (gistId)
import Gists (mkNewGist)
import Halogen (Component, action)
import Halogen as H
import Halogen.Component (ParentHTML)
import Halogen.ECharts (EChartsEffects)
import Halogen.ECharts as EC
import Halogen.HTML (ClassName(ClassName), HTML, a, div, div_, h1, strong_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, href)
import Halogen.Query (HalogenM)
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (CompilationError(CompilationError, RawError))
import Ledger.Ada.TH (Ada(..))
import LocalStorage (LOCALSTORAGE)
import LocalStorage as LocalStorage
import Network.HTTP.Affjax (AJAX)
import Network.RemoteData (RemoteData(NotAsked, Loading, Failure, Success), _Success, isSuccess)
import Playground.API (Evaluation(Evaluation), EvaluationResult(EvaluationResult), SimulatorWallet(SimulatorWallet), SourceCode(SourceCode), _CompilationResult, _FunctionSchema)
import Playground.Server (SPParams_, getOauthStatus, patchGistsByGistId, postContract, postEvaluate, postGists)
import Prelude (type (~>), Unit, Void, bind, const, discard, flip, map, pure, show, unit, unless, void, when, ($), (&&), (+), (-), (<$>), (<*>), (<<<), (<>), (==), (>>=))
import Servant.PureScript.Settings (SPSettings_)
import StaticData (bufferLocalStorageKey)
import StaticData as StaticData
import Wallet.Emulator.Types (Wallet(Wallet))

mkSimulatorWallet :: Int -> SimulatorWallet
mkSimulatorWallet id =
  SimulatorWallet { simulatorWalletWallet: Wallet { getWallet: id }
                  , simulatorWalletBalance: Ada {getAda: 10}
                  }

initialState :: State
initialState =
  { view: Editor
  , compilationResult: NotAsked
  , wallets: mkSimulatorWallet <$> 1..2
  , simulation: Nothing
  , evaluationResult: NotAsked
  , authStatus: NotAsked
  , createGistResult: NotAsked
  }

------------------------------------------------------------

mainFrame ::
  forall m aff.
  MonadAff (EChartsEffects (AceEffects (localStorage :: LOCALSTORAGE, file :: FILE, ajax :: AJAX, analytics :: ANALYTICS | aff))) m
  => MonadAsk (SPSettings_ SPParams_) m
  => Component HTML Query Unit Void m
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
  forall m aff.
  MonadAff (localStorage :: LOCALSTORAGE, file :: FILE, ace :: ACE, ajax :: AJAX, analytics :: ANALYTICS | aff) m
  => MonadAsk (SPSettings_ SPParams_) m
  => Query ~> HalogenM State Query ChildQuery ChildSlot Void m
evalWithAnalyticsTracking query = do
  liftEff $ analyticsTracking query
  eval query

analyticsTracking :: forall eff a. Query a -> Eff (analytics :: ANALYTICS | eff) Unit
analyticsTracking query = do
  case toEvent query of
    Nothing -> pure unit
    Just event -> trackEvent event

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
toEvent :: forall a. Query a -> Maybe Event
toEvent (HandleEditorMessage _ _) = Nothing
toEvent (HandleDragEvent _ _) = Nothing
toEvent (HandleDropEvent _ _) = Just $ defaultEvent "DropScript"
toEvent (HandleMockchainChartMessage _ _) = Nothing
toEvent (HandleBalancesChartMessage _ _) = Nothing
toEvent (CheckAuthStatus _) = Nothing
toEvent (PublishGist _) = Just $ (defaultEvent "Publish") { label = Just "Gist"}
toEvent (ChangeView view _) = Just $ (defaultEvent "View") { label = Just $ show view}
toEvent (LoadScript script a) = Just $ (defaultEvent "LoadScript") { label = Just script}
toEvent (CompileProgram a) = Just $ defaultEvent "CompileProgram"
toEvent (ScrollTo _ _) = Nothing
toEvent (AddWallet _) = Just $ (defaultEvent "AddWallet") { category = Just "Wallet" }
toEvent (RemoveWallet _ _) = Just $ (defaultEvent "RemoveWallet") { category = Just "Wallet" }
toEvent (SetBalance _ _ _) = Just $ (defaultEvent "SetBalance") { category = Just "Wallet" }
toEvent (ModifyActions (AddAction _) _) = Just $ (defaultEvent "AddAction") { category = Just "Action" }
toEvent (ModifyActions (AddWaitAction _) _) = Just $ (defaultEvent "AddWaitAction") { category = Just "Action" }
toEvent (ModifyActions (RemoveAction _) _) = Just $ (defaultEvent "RemoveAction") { category = Just "Action" }
toEvent (ModifyActions (SetWaitTime _ _) _) = Just $ (defaultEvent "SetWaitTime") { category = Just "Action" }
toEvent (EvaluateActions _) = Just $ (defaultEvent "EvaluateActions") { category = Just "Action" }
toEvent (PopulateAction _ _ _) = Just $ (defaultEvent "PopulateAction") { category = Just "Action" }

saveBuffer :: forall eff. String -> Eff (localStorage :: LOCALSTORAGE | eff) Unit
saveBuffer text = LocalStorage.setItem bufferLocalStorageKey text

eval ::
  forall m aff.
  MonadAff (localStorage :: LOCALSTORAGE, file :: FILE, ace :: ACE, ajax :: AJAX | aff) m
  => MonadAsk (SPSettings_ SPParams_) m
  => Query ~> HalogenM State Query ChildQuery ChildSlot Void m
eval (HandleEditorMessage (TextChanged text) next) = do
  liftEff $ saveBuffer text
  pure next

eval (HandleDragEvent event next) = do
  liftEff $ preventDefault event
  pure next

eval (HandleDropEvent event next) = do
  liftEff $ preventDefault event
  contents <- liftAff $ readFileFromDragEvent event
  void $ withEditor $ Editor.setValue contents (Just 1)
  pure next

eval (HandleMockchainChartMessage EC.Initialized next) = do
  updateChartsIfPossible
  pure next

-- We just ignore most ECharts events.
eval (HandleMockchainChartMessage (EC.EventRaised event) next) =
  pure next

eval (HandleBalancesChartMessage EC.Initialized next) = do
  updateChartsIfPossible
  pure next

-- We just ignore most ECharts events.
eval (HandleBalancesChartMessage (EC.EventRaised event) next) =
  pure next

eval (CheckAuthStatus next) = do
  authResult <- runAjaxTo _authStatus getOauthStatus
  pure next

eval (PublishGist next) = do
  mContents <- withEditor Editor.getValue
  case mkNewGist mContents of
    Nothing -> pure next
    Just newGist ->
      do mGist <- use _createGistResult
         let apiCall = case preview (_Success <<< gistId) mGist of
               Nothing -> postGists newGist
               Just gistId -> patchGistsByGistId newGist gistId
         void $ runAjaxTo _createGistResult  apiCall

         pure next

eval (ChangeView view next) = do
  assign _view view
  pure next

eval (LoadScript key next) = do
  case Map.lookup key StaticData.demoFiles of
    Nothing -> pure next
    Just contents -> do
      void $ withEditor $ Editor.setValue contents (Just 1)
      assign _evaluationResult NotAsked
      assign _compilationResult NotAsked
      pure next

eval (CompileProgram next) = do
  mContents <- withEditor Editor.getValue

  case mContents of
    Nothing -> pure next
    Just contents -> do
      result <- runAjaxTo _compilationResult $ postContract $ SourceCode contents

      -- If we got a successful result, switch tab.
      case result of
        Success (Left _) -> pure unit
        _ -> replaceViewOnSuccess result Editor Simulation

      -- Update the error display.
      void $ withEditor $ showCompilationErrorAnnotations $
        case result of
          Success (Left errors) -> errors
          _ -> []

      -- If we have a result with new signatures, we can only hold
      -- onto the old actions if the signatures still match. Any
      -- change means we'll have to clear out the existing simulation.
      case preview (_Success <<< _Right <<< _CompilationResult <<< _functionSchema) result of
        Just newSignatures -> do
          oldSignatures <- use (_simulation <<< _Just <<< _signatures)
          unless (oldSignatures `gEq` newSignatures)
            (assign _simulation (Just { signatures: newSignatures, actions: [] }))
        _ -> pure unit

      pure next

eval (ScrollTo {row, column} next) = do
  void $ withEditor $ Editor.gotoLine row (Just column) (Just true)
  pure next

eval (ModifyActions actionEvent next) = do
  modifying (_simulation <<< _Just <<< _actions) (evalActionEvent actionEvent)
  pure next

eval (EvaluateActions next) = do
  mContents <- withEditor $ Editor.getValue
  _ <- runMaybeT $
       do contents <- MaybeT $ withEditor $ Editor.getValue
          evaluation <- MaybeT $ currentEvaluation (SourceCode contents)
          result <- lift $ runAjaxTo  _evaluationResult $ postEvaluate evaluation

          replaceViewOnSuccess result Simulation Transactions

          lift updateChartsIfPossible

          pure unit
  pure next

eval (AddWallet next) = do
  wallets <- use _wallets
  let maxWalletId = fromMaybe 0 $ maximumOf (traversed <<< _simulatorWalletWallet <<< _walletId) wallets
  let newWallet = mkSimulatorWallet (maxWalletId + 1)
  modifying _wallets (flip Array.snoc newWallet)
  pure next

eval (RemoveWallet index next) = do
  modifying _wallets (fromMaybe <*> Array.deleteAt index)
  assign (_simulation <<< _Just <<< _actions) []
  pure next

eval (SetBalance wallet newBalance next) = do
  modifying _wallets
    (map (\simulatorWallet -> if view _simulatorWalletWallet simulatorWallet == wallet
                              then set _simulatorWalletBalance newBalance simulatorWallet
                              else simulatorWallet))
  pure next

eval (PopulateAction n l event) = do
  modifying
    (_simulation
       <<< _Just
       <<< _actions
       <<< ix n
       <<< _Action
       <<< _functionSchema
       <<< _FunctionSchema
       <<< _argumentSchema
       <<< ix l)
    (evalForm event)
  pure $ extract event

evalActionEvent :: ActionEvent -> Array Action -> Array Action
evalActionEvent (AddAction action) = flip Array.snoc action
evalActionEvent (AddWaitAction blocks) = flip Array.snoc (Wait { blocks })
evalActionEvent (RemoveAction index) = fromMaybe <*> Array.deleteAt index
evalActionEvent (SetWaitTime index time) = set (ix index <<< _Wait <<< _blocks) time

evalForm :: forall a. FormEvent a -> SimpleArgument -> SimpleArgument
evalForm (SetIntField n next) (SimpleInt _) = SimpleInt n
evalForm (SetIntField _ _) arg = arg

evalForm (SetStringField s next) (SimpleString _) = SimpleString (Just s)
evalForm (SetStringField _ _) arg = arg

evalForm (SetSubField 1 subEvent) (SimpleTuple fields) = SimpleTuple $ over _1 (evalForm subEvent) fields
evalForm (SetSubField 2 subEvent) (SimpleTuple fields) = SimpleTuple $ over _2 (evalForm subEvent) fields
evalForm (SetSubField _ subEvent) arg@(SimpleTuple fields) = arg
evalForm (SetSubField _ subEvent) arg@(SimpleString fields) = arg
evalForm (SetSubField _ subEvent) arg@(SimpleInt fields) = arg

evalForm (AddSubField _) (SimpleArray schema fields) =
  -- As the code stands, this is the only guarantee we get that every
  -- value in the array will conform to the schema: the fact that we
  -- create the 'empty' version from the same schema template.
  --
  -- Is more type safety than that possible? Probably.
  -- Is it worth the research effort? Perhaps. :thinking_face:
  SimpleArray schema $ Array.snoc fields (toValue schema)
evalForm (AddSubField _) arg = arg

evalForm (SetSubField n subEvent) (SimpleArray schema fields) =
  SimpleArray schema $ over (ix n) (evalForm subEvent) fields

evalForm (SetSubField n subEvent) s@(SimpleObject schema fields) =
  SimpleObject schema $ over (ix n <<< _2) (evalForm subEvent) fields
evalForm (SetSubField n subEvent) arg@(Unknowable _) = arg

evalForm (RemoveSubField n subEvent) arg@(SimpleArray schema fields ) =
  (SimpleArray schema (fromMaybe fields (Array.deleteAt n fields)))
evalForm (RemoveSubField n subEvent) arg =
  arg

replaceViewOnSuccess :: forall m e a. MonadState State m => RemoteData e a -> View -> View -> m Unit
replaceViewOnSuccess result source target = do
  currentView <- use _view
  when (isSuccess result && currentView == source)
    (assign _view target)

currentEvaluation :: forall m. MonadState State m => SourceCode -> m (Maybe Evaluation)
currentEvaluation sourceCode = do
  wallets <- use _wallets
  simulation <- use _simulation
  pure $ do
    {actions} <- simulation
    program <- traverse toExpression actions
    pure $ Evaluation { wallets
                      , program
                      , sourceCode
                      , blockchain: []
                      }

updateChartsIfPossible :: forall m i o. HalogenM State i ChildQuery ChildSlot o m Unit
updateChartsIfPossible = do
  use _evaluationResult >>= case _ of
    Success (EvaluationResult result) -> do
      void $ H.query' cpMockchainChart MockchainChartSlot $ H.action $ EC.Set $ interpret $ mockchainChartOptions result.resultGraph
      void $ H.query' cpBalancesChart BalancesChartSlot $ H.action $ EC.Set $ interpret $ balancesChartOptions result.fundsDistribution
    _ -> pure unit

------------------------------------------------------------

-- | Handles the messy business of running an editor command iff the
-- editor is up and running.
withEditor :: forall m eff a.
  MonadEff (ace :: ACE | eff) m
  => (Editor -> Eff (ace :: ACE | eff) a)
  -> HalogenM State Query ChildQuery ChildSlot Void m (Maybe a)
withEditor action = do
  mEditor <- H.query' cpEditor EditorSlot $ H.request GetEditor
  case mEditor of
    Just (Just editor) -> do
      liftEff $ Just <$> action editor
    _ -> pure Nothing

showCompilationErrorAnnotations :: forall m.
  Array CompilationError
  -> Editor
  -> Eff (ace :: ACE | m) Unit
showCompilationErrorAnnotations errors editor = do
  session <- Editor.getSession editor
  Session.setAnnotations (catMaybes (toAnnotation <$> errors)) session

toAnnotation :: CompilationError -> Maybe Annotation
toAnnotation (RawError _) = Nothing
toAnnotation (CompilationError {row, column, text}) =
  Just
    { type: "error"
    , row: row - 1
    , column
    , text: String.joinWith "\n" text
    }

render ::
  forall m aff.
  MonadAff (EChartsEffects (AceEffects (localStorage :: LOCALSTORAGE | aff))) m
  => State -> ParentHTML Query ChildQuery ChildSlot m
render state =
  div
    [ class_ $ ClassName "main-frame" ]
    [ container_
        [ mainHeader
        , mainTabBar state.view
        ]
    , viewContainer state.view Editor $
        [ editorPane state
        ]
    , viewContainer state.view Simulation $
        case state.compilationResult, state.simulation of
          Success (Left error), _ ->
            [ text "Your contract has errors. Click the "
            , strong_ [ text "Editor" ]
            , text " tab above to fix them and recompile."
            ]
          Success (Right _), Just simulation ->
            [ simulationPane
                simulation
                state.wallets
                state.evaluationResult
            ]
          Failure error, _ -> [ ajaxErrorPane error ]
          Loading, _ -> [ icon Spinner ]
          _, _ ->
            [ text "Click the "
            , strong_ [ text "Editor" ]
            , text " tab above and compile a contract to get started."
            ]
    , viewContainer state.view Transactions $
        case state.evaluationResult of
          Success evaluation ->
            [ evaluationPane evaluation ]
          Failure error -> [ ajaxErrorPane error ]
          Loading -> [ icon Spinner ]
          NotAsked ->
            [ text "Click the "
            , strong_ [ text "Simulation"  ]
            , text " tab above and evaluate a simulation to see some results."
            ]
    ]

viewContainer :: forall p i. View -> View -> Array (HTML p i) -> HTML p i
viewContainer currentView targetView =
  if currentView == targetView
  then div [ classes [ container ] ]
  else div [ classes [ container, hidden ] ]

mainHeader :: forall p. HTML p (Query Unit)
mainHeader =
  div_
    [ div [ classes [ btnGroup, pullRight ] ]
        (makeLink <$> links)
    , h1
        [ class_ $ ClassName "main-title" ]
        [ text "Plutus Playground" ]
    ]
  where
    links = [ Tuple "Getting Started" "https://testnet.iohkdev.io/plutus/get-started/writing-contracts-in-plutus/"
            , Tuple "Tutorial" "https://github.com/input-output-hk/plutus/blob/master/plutus-tutorial/tutorial/Tutorial/02-wallet-api.md"
            , Tuple "API" "https://input-output-hk.github.io/plutus/"
            , Tuple "Privacy" "https://static.iohk.io/docs/data-protection/iohk-data-protection-gdpr-policy.pdf"
            ]
    makeLink (Tuple name link) =
      a [ classes [ btn, btnSmall ]
        , href link
        ]
        [ text name ]

mainTabBar :: forall p. View -> HTML p (Query Unit)
mainTabBar activeView =
  navTabs_ (mkTab <$> tabs)
  where
    tabs = [ Editor /\ "Editor"
           , Simulation /\ "Simulation"
           , Transactions /\ "Transactions"
           ]
    mkTab (link /\ title ) =
      navItem_ [
        a
          [ classes $ [ navLink ] <> activeClass
          , onClick $ const $ Just $ action $ ChangeView link
          ]
          [ text title ]
      ]
      where
        activeClass =
          if link == activeView
          then [ active ]
          else []
