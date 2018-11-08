module MainFrame
  ( mainFrame
  ) where

import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceEffects, AceMessage(..), AceQuery(..), Autocomplete(..), aceComponent)
import Ace.Types (ACE, Editor, Annotation)
import Action (actionsPane)
import AjaxUtils (showAjaxError)
import Bootstrap (alertDanger_, btn, btnBlock, btnDanger, btnPrimary, btnSecondary, btnSuccess, col2_, col7_, col_, container_, empty, listGroupItem_, listGroup_, pullRight, row_)
import Control.Monad.Aff.Class (class MonadAff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Monad.Except (ExceptT)
import Control.Monad.Except.Trans (runExceptT)
import Control.Monad.Reader (ReaderT)
import Control.Monad.Reader.Class (class MonadAsk, ask)
import Control.Monad.Reader.Trans (runReaderT)
import Data.Array (catMaybes)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Either.Nested (Either2)
import Data.Foldable (traverse_)
import Data.Functor.Coproduct.Nested (Coproduct2)
import Data.Lens (assign, modifying, use)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Show (show)
import Data.String as String
import Data.Tuple.Nested ((/\))
import ECharts.Commands as E
import ECharts.Monad (CommandsT, interpret)
import ECharts.Types.Phantom (I)
import Halogen (Component)
import Halogen as H
import Halogen.Component (ParentHTML)
import Halogen.Component.ChildPath (ChildPath, cp1, cp2)
import Halogen.ECharts (EChartsEffects, EChartsQuery, echarts)
import Halogen.ECharts as EC
import Halogen.HTML (ClassName(ClassName), HTML, a, br_, button, code_, div, div_, h1_, h3_, p_, slot', small, strong_, text)
import Halogen.HTML.Events (input, input_, onClick)
import Halogen.HTML.Properties (class_, classes, disabled, href, target)
import Halogen.Query (HalogenM)
import Icons (Icon(..), icon)
import Network.HTTP.Affjax (AJAX)
import Network.RemoteData (RemoteData(..), isLoading)
import Network.RemoteData as RemoteData
import Playground.API (CompilationError(..), SourceCode(..))
import Playground.Server (SPParams_, postContract)
import Prelude (class Eq, class Monad, class Ord, type (~>), Unit, Void, bind, const, discard, flip, pure, unit, void, ($), (+), (<$>), (<*>), (<<<), (<>), (>>=))
import Servant.PureScript.Settings (SPSettings_)
import StaticData as StaticData
import Types (Balance, Query(..), State, Transfer, WalletId(..), Evaluation, _actions, _compilationResult, _editorContents, _evaluation, _wallets)
import Wallet (walletsPane)

initialState :: State
initialState =
  { actions: []
  , wallets: StaticData.wallets
  , evaluation: NotAsked
  , editorContents: StaticData.editorContents
  , compilationResult: NotAsked
  }

type ChildQuery = Coproduct2 AceQuery EChartsQuery
type ChildSlot = Either2 AceSlot EChartsSlot

data AceSlot = AceSlot
derive instance eqComponentAceSlot :: Eq AceSlot
derive instance ordComponentAceSlot :: Ord AceSlot

data EChartsSlot = EChartsSlot
derive instance eqComponentEChartsSlot :: Eq EChartsSlot
derive instance ordComponentEChartsSlot :: Ord EChartsSlot

cpAce :: ChildPath AceQuery ChildQuery AceSlot ChildSlot
cpAce = cp1

cpECharts :: ChildPath EChartsQuery ChildQuery EChartsSlot ChildSlot
cpECharts = cp2

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
eval (HandleAceMessage (TextChanged text) next) = do
  assign _editorContents text
  pure next

eval (HandleEChartsMessage EC.Initialized next) = do
  updateChartIfPossible
  pure next

-- We just ignore most ECharts events.
eval (HandleEChartsMessage (EC.EventRaised event) next) =
  pure next

eval (CompileProgram next) = do
  contents <- use _editorContents
  --
  assign _compilationResult Loading
  result <- runAjax $ postContract $ SourceCode contents
  assign _compilationResult result
  --
  withEditor $ showCompilationErrorAnnotations $
    case result of
      Success (Left errors) -> errors
      _ -> []
  --
  -- TODO We need to think about clearing out the list of actions. If
  --   the code has changed, the actions might be invalid. But we don't
  --   really want to kill them off unless they are invalid or it's
  --   annoying for the user.
  --
  -- One option is to leave them alone and let any errors be part of
  --   the "submit actions" feedback.
  --
  pure next

eval (ScrollTo {row, column} next) = do
  withEditor $ Editor.gotoLine row (Just column) (Just true)
  pure next

eval (SendAction action next) = do
  modifying _actions $ flip Array.snoc action
  pure next

eval (KillAction index next) = do
  modifying _actions (fromMaybe <*> Array.deleteAt index)
  pure next

eval (EvaluateActions next) = do
  assign _evaluation $ Success StaticData.evaluation
  updateChartIfPossible
  pure next

eval (AddWallet next) = do
  count <- Array.length <$> use _wallets
  let newWallet =
        { walletId: WalletId (show (count + 1))
        , balance: 10.0
        }
  modifying _wallets (flip Array.snoc newWallet)
  pure next

eval (RemoveWallet index next) = do
  modifying _wallets (fromMaybe <*> Array.deleteAt index)
  assign _actions []
  pure next

updateChartIfPossible :: forall m i o. HalogenM State i ChildQuery ChildSlot o m Unit
updateChartIfPossible = do
  use _evaluation >>= case _ of
    Success evaluation ->
      void $ H.query' cpECharts EChartsSlot $ H.action $ EC.Set $ interpret $ sankeyDiagramOptions evaluation
    _ -> pure unit

------------------------------------------------------------

-- | Handles the messy business of running an editor command iff the
-- editor is up and running.
withEditor :: forall m eff.
  MonadEff (ace :: ACE | eff) m
  => (Editor -> Eff (ace :: ACE | eff) Unit)
  -> HalogenM State Query ChildQuery ChildSlot Void m Unit
withEditor action = do
  mEditor <- H.query' cpAce AceSlot $ H.request GetEditor
  case mEditor of
    Just (Just editor) -> liftEff $ action editor
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

initEditor ∷
  forall m aff.
  MonadAff (ace :: ACE | aff) m
  => String -> Editor -> m Unit
initEditor contents editor = liftEff $ do
  void $ Editor.setValue contents (Just 1) editor
  --
  session <- Editor.getSession editor
  Session.setMode "ace/mode/haskell" session

render ::
  forall m aff.
  MonadAff (EChartsEffects (AceEffects aff)) m
  => State -> ParentHTML Query ChildQuery ChildSlot m
render state =
  div [ class_ (ClassName "main-frame") ] $
    [ container_
      [ header
      , br_
      , editorPane state
      , br_
      , case state.compilationResult of
          Success (Right _) -> mockChainPane state
          _ -> empty
      ]
    ]

header :: forall p i. HTML p i
header =
  row_
    [ col_ [ h1_ [ text "Plutus Playground" ] ]
    , col_
      [ p_ [
          a [ href "https://github.com/input-output-hk/plutus/tree/mchakravarty/plutus-playground-spec/docs/playground"
            , target "_blank"
            ]
            [ text "Design Document" ]
          ]
      ]
    ]

editorPane ::
  forall m aff.
  MonadAff (EChartsEffects (AceEffects aff)) m
  => State -> ParentHTML Query ChildQuery ChildSlot m
editorPane state =
  div_
    [ slot' cpAce AceSlot
        (aceComponent (initEditor state.editorContents) (Just Live))
        unit
        (input HandleAceMessage)
    , br_
    , row_
        [ col2_
            [ button [ classes [ btn
                               , btnBlock
                               , btnClass
                               ]
                     , onClick $ input_ CompileProgram
                     , disabled (isLoading state.compilationResult)
                     ]
                [ btnText ]
            ]
        , col_ [ errorList ]
        ]
    ]
    where
      btnClass = case state.compilationResult of
                   Success (Right _) -> btnSuccess
                   Success (Left _) -> btnDanger
                   Failure _ -> btnDanger
                   Loading -> btnSecondary
                   NotAsked -> btnPrimary
      btnText = case state.compilationResult of
                   Loading -> icon Spinner
                   _ -> text "Compile"
      errorList = case state.compilationResult of
                    (Success (Left errors)) ->
                      listGroup_
                        (listGroupItem_ <<< pure <<< compilationErrorPane <$> errors)
                    Failure error ->
                      alertDanger_
                        [ text $ showAjaxError error
                        , br_
                        , text "Please try again or contact support for assistance."
                        ]
                    _ -> empty


compilationErrorPane :: forall p. CompilationError -> HTML p (Query Unit)
compilationErrorPane (RawError error) =
  div_ [ text error ]
compilationErrorPane (CompilationError error) =
  div [ class_ $ ClassName "compilation-error"
      , onClick $ input_ $ ScrollTo {row: error.row, column: error.column}
      ]
    [ small [ class_ pullRight ]
        [ text "jump" ]
    , strong_
        [ text $ "Line " <> show error.row <> ", Column " <> show error.column <> ":" ]
    , br_
    , code_
        [ text $ String.joinWith "\n" error.text ]
    ]

mockChainPane ::
  forall m aff.
  MonadAff (EChartsEffects (AceEffects aff)) m
  => State -> ParentHTML Query ChildQuery ChildSlot m
mockChainPane state =
  div_
    [ row_
        [ col7_ [ walletsPane state.wallets ]
        , col_ [ actionsPane state.actions  ]
        ]
    , div_
        case state.evaluation of
          Success evaluation ->
            [ h3_ [ text "Chain" ]
            , slot' cpECharts EChartsSlot
             (echarts Nothing)
             ({width: 800, height: 800} /\ unit)
             (input HandleEChartsMessage)
            ]
          _ -> []
    ]

------------------------------------------------------------

toItem :: forall m i. Monad m => Balance -> CommandsT (item :: I | i) m Unit
toItem {name, value} =
  E.addItem do
    E.name name
    E.value value

toLink :: forall m i. Monad m => Transfer -> CommandsT (link :: I | i) m Unit
toLink {source, target, value} =
  E.addLink do
    E.sourceName source
    E.targetName target
    E.value value

toChartOptions :: forall m i. Monad m => Evaluation -> CommandsT (series :: I | i) m Unit
toChartOptions {balances, transfers} =
  E.series $ E.sankey do
    E.buildItems (traverse_ toItem balances)
    E.buildLinks (traverse_ toLink transfers)

sankeyDiagramOptions :: forall m i. Monad m => Evaluation -> CommandsT (series :: I | i) m Unit
sankeyDiagramOptions {balances, transfers} =
  E.series $ E.sankey do
    E.buildItems (traverse_ toItem balances)
    E.buildLinks (traverse_ toLink transfers)

runAjax ::
  forall m env a e.
  MonadAsk env m
  => ReaderT env (ExceptT e m) a -> m (RemoteData e a)
runAjax action = do
  settings <- ask
  result <- runExceptT $ runReaderT action settings
  pure $ RemoteData.fromEither result
