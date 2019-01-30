module MainFrame
  ( mainFrame
  ) where

import Types

import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceEffects, AceMessage(TextChanged), AceQuery(GetEditor))
import Ace.Types (ACE, Editor, Annotation)
import Action (simulationPane)
import AjaxUtils (ajaxErrorPane, runAjax)
import Analytics (Event, defaultEvent, trackEvent, ANALYTICS)
import Bootstrap (btn, btnGroup, btnSmall, container_, empty, pullRight)
import Chain (mockchainChartOptions, balancesChartOptions, evaluationPane)
import Control.Comonad (extract)
import Control.Monad.Aff.Class (class MonadAff, liftAff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Monad.Reader.Class (class MonadAsk)
import Control.Monad.State (class MonadState)
import Data.Argonaut.Core (Json)
import Data.Argonaut.Core as Json
import Data.Array (catMaybes, (..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic (gEq)
import Data.Int as Int
import Data.Lens (_2, assign, maximumOf, modifying, over, set, to, traversed, use, view)
import Data.Lens.Index (ix)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.RawJson (RawJson(..))
import Data.StrMap as M
import Data.String as String
import Data.Tuple (Tuple(Tuple))
import Data.Tuple.Nested ((/\))
import ECharts.Monad (interpret)
import Editor (editorPane)
import FileEvents (FILE, preventDefault, readFileFromDragEvent)
import Halogen (Component)
import Halogen as H
import Halogen.Component (ParentHTML)
import Halogen.ECharts (EChartsEffects)
import Halogen.ECharts as EC
import Halogen.HTML (ClassName(ClassName), HTML, a, div, div_, h1, text)
import Halogen.HTML.Properties (class_, classes, href)
import Halogen.Query (HalogenM)
import LocalStorage (LOCALSTORAGE)
import LocalStorage as LocalStorage
import Network.HTTP.Affjax (AJAX)
import Network.RemoteData (RemoteData(Success, Failure, Loading, NotAsked))
import Playground.API (CompilationError(CompilationError, RawError), Evaluation(Evaluation), EvaluationResult(EvaluationResult), SourceCode(SourceCode), _FunctionSchema, _CompilationResult)
import Playground.API as API
import Playground.Server (SPParams_, postContract, postEvaluate)
import Prelude (type (~>), Unit, Void, bind, const, discard, flip, map, pure, unit, void, ($), (+), (-), (<$>), (<*>), (<<<), (>>=))
import Servant.PureScript.Settings (SPSettings_)
import StaticData (bufferLocalStorageKey)
import StaticData as StaticData
import Wallet.Emulator.Types (Wallet(..), _Wallet)

initialState :: State
initialState =
  { compilationResult: NotAsked
  , wallets: (\n -> MockWallet { wallet: Wallet { getWallet: n }, balance: 10 }) <$> 1..2
  , actions: []
  , evaluationResult: NotAsked
  }

------------------------------------------------------------

mainFrame ::
  forall m aff.
  MonadAff (EChartsEffects (AceEffects (localStorage :: LOCALSTORAGE, file :: FILE, ajax :: AJAX, analytics :: ANALYTICS | aff))) m
  => MonadAsk (SPSettings_ SPParams_) m
  => Component HTML Query Unit Void m
mainFrame =
  H.parentComponent
    { initialState: const initialState
    , render
    , eval: evalWithAnalyticsTracking
    , receiver: const Nothing
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
toEvent (LoadScript script a) = Just $ (defaultEvent "LoadScript") { label = Just script}
toEvent (CompileProgram a) = Just $ defaultEvent "CompileProgram"
toEvent (ScrollTo _ _) = Nothing
toEvent (AddWallet _) = Just $ (defaultEvent "AddWallet") { category = Just "Wallet" }
toEvent (RemoveWallet _ _) = Just $ (defaultEvent "RemoveWallet") { category = Just "Wallet" }
toEvent (SetBalance _ _ _) = Just $ (defaultEvent "SetBalance") { category = Just "Wallet" }
toEvent (AddAction _ _) = Just $ (defaultEvent "AddAction") { category = Just "Action" }
toEvent (AddWaitAction _ _) = Just $ (defaultEvent "AddWaitAction") { category = Just "Action" }
toEvent (RemoveAction _ _) = Just $ (defaultEvent "RemoveAction") { category = Just "Action" }
toEvent (EvaluateActions _) = Just $ (defaultEvent "EvaluateActions") { category = Just "Action" }
toEvent (PopulateAction _ _ _) = Just $ (defaultEvent "PopulateAction") { category = Just "Action" }
toEvent (SetWaitTime _ _ _) = Just $ (defaultEvent "SetWaitTime") { category = Just "Action" }

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

eval (LoadScript key next) = do
  case Map.lookup key StaticData.demoFiles of
    Nothing -> pure next
    Just contents -> do
      void $ withEditor $ Editor.setValue contents (Just 1)
      assign _evaluationResult NotAsked
      assign _compilationResult NotAsked
      assign _actions []
      pure next

eval (CompileProgram next) = do
  mContents <- withEditor Editor.getValue
  case mContents of
    Nothing -> pure next
    Just contents ->  do
      assign _compilationResult Loading
      result <- runAjax $ postContract $ SourceCode contents
      assign _compilationResult result

      void $ withEditor $ showCompilationErrorAnnotations $
        case result of
          Success (Left errors) -> errors
          _ -> []
      pure next

eval (ScrollTo {row, column} next) = do
  void $ withEditor $ Editor.gotoLine row (Just column) (Just true)
  pure next

eval (AddAction action next) = do
  modifying _actions $ flip Array.snoc action
  pure next

eval (AddWaitAction blocks next) = do
  modifying _actions $ flip Array.snoc (Wait { blocks })
  pure next

eval (RemoveAction index next) = do
  modifying _actions (fromMaybe <*> Array.deleteAt index)
  pure next

eval (EvaluateActions next) = do
  mContents <- withEditor $ Editor.getValue
  case mContents of
    Nothing -> pure next
    Just contents -> do
      evaluation <- currentEvaluation (SourceCode contents)
      assign _evaluationResult Loading
      result <- runAjax $ postEvaluate evaluation
      assign _evaluationResult result
      --
      updateChartsIfPossible
      pure next

eval (AddWallet next) = do
  wallets <- use _wallets
  let maxWalletId = fromMaybe 0 $ maximumOf (traversed <<< _MockWallet <<< _wallet <<< _Wallet <<< to _.getWallet ) wallets
  let newWallet = MockWallet
        { wallet: Wallet { getWallet: (maxWalletId + 1) }
        , balance: 10
        }
  modifying _wallets (flip Array.snoc newWallet)
  pure next

eval (RemoveWallet index next) = do
  modifying _wallets (fromMaybe <*> Array.deleteAt index)
  assign _actions []
  pure next

eval (SetBalance wallet newBalance next) = do
  modifying _wallets
    (map (\mockWallet -> if view (_MockWallet <<< _wallet) mockWallet  `gEq` wallet
                         then set (_MockWallet <<< _balance) newBalance mockWallet
                         else mockWallet))
  pure next

eval (PopulateAction n l event) = do
  modifying
    (_actions
       <<< ix n
       <<< _Action
       <<< _functionSchema
       <<< _FunctionSchema
       <<< _argumentSchema
       <<< ix l)
    (evalForm event)
  pure $ extract event

eval (SetWaitTime index time next) = do
  assign
    (_actions
       <<< ix index
       <<< _Wait
       <<< _blocks)
    time
  pure next

evalForm :: forall a. FormEvent a -> SimpleArgument -> SimpleArgument
evalForm (SetIntField n next) (SimpleInt _) = SimpleInt n
evalForm (SetStringField s next) (SimpleString _) = SimpleString (Just s)
evalForm (SetSubField n subEvent) old@(SimpleObject fields) =
  case Array.index fields n of
    Nothing -> old
    Just (name /\ oldArg) ->
      let newArg = evalForm subEvent oldArg
      in case Array.updateAt n (name /\ newArg) fields of
           Nothing -> old
           Just newFields -> SimpleObject newFields
evalForm other arg = arg

currentEvaluation :: forall m. MonadState State m => SourceCode -> m Evaluation
currentEvaluation sourceCode = do
  actions <- use _actions
  let toPair :: MockWallet -> Tuple Wallet Int
      toPair mockWallet =
        view (_MockWallet <<< _wallet) mockWallet
        /\
        view (_MockWallet <<< _balance) mockWallet
  wallets <- map toPair <$> use _wallets
  let program = toExpression <$> actions
  let blockchain = []
  pure $ Evaluation { wallets, program, sourceCode, blockchain }

toExpression :: Action -> API.Expression
toExpression (Wait wait) = API.Wait wait
toExpression (Action action) = API.Action
  { wallet: view (_MockWallet <<< _wallet) action.mockWallet
  , function: functionSchema.functionName
  , arguments: jsonArguments
  }
  where
    functionSchema = unwrap $ action.functionSchema
    jsonArguments = RawJson <<< Json.stringify <<< toJson <$> functionSchema.argumentSchema
    toJson :: SimpleArgument -> Json
    toJson (SimpleInt (Just str)) = Json.fromNumber $ Int.toNumber str
    toJson (SimpleString (Just str)) = Json.fromString str
    toJson (SimpleObject fields) =
      Json.fromObject $ M.fromFoldable $ over (traversed <<< _2) toJson fields
    toJson _ = Json.fromNull Json.jNull -- TODO

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
        , editorPane state
        ]
    , stripeContainer_ [
        case state.compilationResult of
          Success (Right compilationResult) ->
            simulationPane (view (_CompilationResult <<< _functionSchema) compilationResult) state.wallets state.actions state.evaluationResult
          Failure error -> ajaxErrorPane error
          _ -> empty
      ]
    , container_ [
        case state.evaluationResult of
          Success evaluation ->
            evaluationPane evaluation
          Failure error -> ajaxErrorPane error
          _ -> empty
      ]
    ]

stripeContainer_ :: forall p i. Array (HTML p i) -> HTML p i
stripeContainer_ children =
  div
    [ class_ $ ClassName "stripe" ]
    [ container_ children ]

mainHeader :: forall p i. HTML p i
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
            , Tuple "Tutorial" "https://github.com/input-output-hk/plutus/blob/master/wallet-api/tutorial/Tutorial.md"
            , Tuple "API" "https://input-output-hk.github.io/plutus/"
            , Tuple "Privacy" "https://static.iohk.io/docs/data-protection/iohk-data-protection-gdpr-policy.pdf"
            ]
    makeLink (Tuple name link) =
      a [ classes [ btn, btnSmall ]
        , href link
        ]
        [ text name ]
