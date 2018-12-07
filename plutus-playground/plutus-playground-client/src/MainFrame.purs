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
import Bootstrap (btn, btnGroup, btnSmall, container_, empty, pullRight)
import Chain (mockchainChartOptions, balancesChartOptions, evaluationPane)
import Control.Comonad (extract)
import Control.Monad.Aff.Class (class MonadAff)
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
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Map as Map
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Newtype (unwrap)
import Data.RawJson (RawJson(..))
import Data.StrMap as M
import Data.String as String
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import ECharts.Monad (interpret)
import Editor (editorPane)
import Halogen (Component)
import Halogen as H
import Halogen.Component (ParentHTML)
import Halogen.ECharts (EChartsEffects)
import Halogen.ECharts as EC
import Halogen.HTML (ClassName(ClassName), HTML, a, div, div_, h1, text)
import Halogen.HTML.Properties (class_, classes, href)
import Halogen.Query (HalogenM)
import Network.HTTP.Affjax (AJAX)
import Network.RemoteData (RemoteData(Success, Failure, Loading, NotAsked))
import Playground.API (CompilationError(CompilationError, RawError), Evaluation(Evaluation), EvaluationResult(EvaluationResult), SourceCode(SourceCode))
import Playground.API as API
import Playground.Server (SPParams_, postContract, postEvaluate)
import Prelude (type (~>), Unit, Void, bind, const, discard, flip, map, pure, unit, void, ($), (+), (<$>), (<*>), (<<<), (>>=))
import Servant.PureScript.Settings (SPSettings_)
import StaticData as StaticData
import Wallet.Emulator.Types (Wallet(..), _Wallet)

initialState :: State
initialState =
  { editorContents: fromMaybe "" $ Map.lookup "Vesting" StaticData.editorContents
  , compilationResult: NotAsked
  , wallets: (\n -> MockWallet { wallet: Wallet { getWallet: n }, balance: 10 }) <$> 1..2
  , actions: []
  , evaluationResult: NotAsked
  }

------------------------------------------------------------

mainFrame ::
  forall m aff.
  MonadAff (EChartsEffects (AceEffects (ajax :: AJAX | aff))) m
  => MonadAsk (SPSettings_ SPParams_) m
  => Component HTML Query Unit Void m
mainFrame =
  H.parentComponent
    { initialState: const initialState
    , render
    , eval
    , receiver: const Nothing
    }

eval ::
  forall m aff.
  MonadAff (ace :: ACE, ajax :: AJAX | aff) m
  => MonadAsk (SPSettings_ SPParams_) m
  => Query ~> HalogenM State Query ChildQuery ChildSlot Void m
eval (HandleEditorMessage (TextChanged text) next) = do
  assign _editorContents text
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
  case Map.lookup key StaticData.editorContents of
    Nothing -> pure unit
    Just contents -> do
      assign _editorContents contents
      withEditor $ Editor.setValue contents (Just 1)
  assign _evaluationResult NotAsked
  assign _compilationResult NotAsked
  assign _actions []
  pure next

eval (CompileProgram next) = do
  contents <- use _editorContents
  --
  assign _evaluationResult NotAsked
  assign _compilationResult Loading
  result <- runAjax $ postContract $ SourceCode contents
  assign _compilationResult result
  --
  withEditor $ showCompilationErrorAnnotations $
    case result of
      Success (Left errors) -> errors
      _ -> []
  --
  pure next

eval (ScrollTo {row, column} next) = do
  withEditor $ Editor.gotoLine row (Just column) (Just true)
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
  -- | TODO This is probably wrong. We ought to be capturing the
  -- successfully-compiled source, so that we use that even if the
  -- editor changes, right?
  contents <- use _editorContents
  evaluation <- currentEvaluation
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
       <<< _Newtype
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

currentEvaluation :: forall m. MonadState State m => m Evaluation
currentEvaluation = do
  actions <- use _actions
  let toPair :: MockWallet -> Tuple Wallet Int
      toPair mockWallet =
        view (_MockWallet <<< _wallet) mockWallet
        /\
        view (_MockWallet <<< _balance) mockWallet
  wallets <- map toPair <$> use _wallets
  let program = toExpression <$> actions
  sourceCode <- SourceCode <$> use _editorContents
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
  -> HalogenM State Query ChildQuery ChildSlot Void m Unit
withEditor action = do
  mEditor <- H.query' cpEditor EditorSlot $ H.request GetEditor
  case mEditor of
    Just (Just editor) -> do
      void $ liftEff $ action editor
      pure unit
    _ -> pure unit

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
    , row
    , column
    , text: String.joinWith "\n" text
    }

render ::
  forall m aff.
  MonadAff (EChartsEffects (AceEffects aff)) m
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
          Success (Right functionSchemas) ->
            simulationPane functionSchemas state.wallets state.actions state.evaluationResult
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
        (makeLink <$> [ Tuple "Getting Started" "https://webdevf.iohk.io/plutus/get-started/writing-contracts-in-plutus/"
                      , Tuple "Tutorial" "https://github.com/input-output-hk/plutus/blob/master/wallet-api/tutorial/Tutorial.md"
                      , Tuple "API" "https://input-output-hk.github.io/plutus/"
                      ])
    , h1
        [ class_ $ ClassName "main-title" ]
        [ text "Plutus Playground" ]
    ]
  where
    makeLink (Tuple name link) =
      a [ classes [ btn, btnSmall ]
        , href link
        ]
        [ text name ]
