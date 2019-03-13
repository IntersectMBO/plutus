module MainFrame
  ( mainFrame
  ) where

import Types

import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceEffects, AceMessage(TextChanged), AceQuery(GetEditor))
import Ace.Types (ACE, Editor, Annotation)
import Action (simulationPane)
import AjaxUtils (ajaxErrorPane, runAjax, runAjaxTo)
import Analytics (Event, defaultEvent, trackEvent, ANALYTICS)
import Bootstrap (active, btn, btnGroup, btnSmall, col10_, col2_, container, container_, empty, hidden, navItem_, navLink, navTabs_, pullRight, row_)
import Chain (mockchainChartOptions, balancesChartOptions, evaluationPane)
import Control.Bind (bindFlipped)
import Control.Comonad (extract)
import Control.Monad.Aff.Class (class MonadAff, liftAff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Reader.Class (class MonadAsk, ask)
import Control.Monad.State (class MonadState)
import Control.Monad.Trans.Class (lift)
import Data.Argonaut.Parser (jsonParser)
import Data.Array (catMaybes, (..))
import Data.Array as Array
import Data.Either (Either(..), note)
import Data.Generic (gEq)
import Data.Lens (_1, _2, _Just, _Right, assign, modifying, over, set, traversed, use, view)
import Data.Lens.Fold (findOf, maximumOf, preview)
import Data.Lens.Index (ix)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.String as String
import Data.Tuple (Tuple(Tuple))
import Data.Tuple.Nested ((/\))
import ECharts.Monad (interpret)
import Editor (editorPane)
import FileEvents (FILE, preventDefault, readFileFromDragEvent)
import Gist (gistFileContent, gistFileFilename, gistFiles, gistId)
import Gists (gistControls, gistSimulationFilename, gistSourceFilename, mkNewGist)
import Gists as Gists
import Halogen (Component, action)
import Halogen as H
import Halogen.Component (ParentHTML)
import Halogen.ECharts (EChartsEffects)
import Halogen.ECharts as EC
import Halogen.HTML (ClassName(ClassName), HTML, a, div, div_, h1, strong_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, href, id_)
import Halogen.Query (HalogenM)
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (CompilationError(CompilationError, RawError))
import Ledger.Ada.TH (Ada(..))
import LocalStorage (LOCALSTORAGE)
import LocalStorage as LocalStorage
import Network.HTTP.Affjax (AJAX)
import Network.RemoteData (RemoteData(NotAsked, Loading, Failure, Success), _Success, isSuccess)
import Playground.API (EvaluationResult(EvaluationResult), SimulatorWallet(SimulatorWallet), SourceCode(SourceCode), _CompilationResult, _FunctionSchema)
import Playground.Server (SPParams_, getGistsByGistId, getOauthStatus, patchGistsByGistId, postContract, postEvaluate, postGists)
import Prelude (type (~>), Unit, Void, bind, const, discard, flip, join, map, pure, show, unit, unless, void, when, ($), (&&), (+), (-), (<$>), (<*>), (<<<), (<>), (=<<), (==), (>>=))
import Servant.PureScript.Settings (SPSettingsDecodeJson_(..), SPSettings_(..))
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
  , simulation: Nothing
  , evaluationResult: NotAsked
  , authStatus: NotAsked
  , createGistResult: NotAsked
  , gistUrl: Nothing
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
toEvent (PublishGist _) = Just $ (defaultEvent "Publish") { category = Just "Gist" }
toEvent (SetGistUrl _ _) = Nothing
toEvent (LoadGist _) = Just $ (defaultEvent "LoadGist") { category = Just "Gist" }
toEvent (ChangeView view _) = Just $ (defaultEvent "View") { label = Just $ show view }
toEvent (LoadScript script a) = Just $ (defaultEvent "LoadScript") { label = Just script }
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
  serverParameters <- ask
  mContents <- getEditorContents
  simulation <- use _simulation
  case mkNewGist serverParameters { source: mContents, simulation } of
    Nothing -> pure next
    Just newGist ->
      do mGist <- use _createGistResult
         let apiCall = case preview (_Success <<< gistId) mGist of
               Nothing -> postGists newGist
               Just gistId -> patchGistsByGistId newGist gistId
         newResult <- runAjax apiCall

         assign _createGistResult newResult

         case preview (_Success <<< gistId) newResult of
               Nothing -> pure unit
               Just gistId -> assign _gistUrl (Just (unwrap gistId))

         pure next

eval (SetGistUrl newGistUrl next) = do
  assign _gistUrl (Just newGistUrl)
  pure next

eval (LoadGist next) = do
  eGistUrl <- (bindFlipped Gists.parseGistUrl <<< note "Gist Url not set.") <$> use _gistUrl
  case eGistUrl of
    Left _ -> pure unit
    Right gistId -> do (SPSettings_ {decodeJson: (SPSettingsDecodeJson_ decodeJson)}) <- ask
                       aGist <- runAjax $ getGistsByGistId gistId
                       case aGist of
                         Success gist -> do
                           assign _createGistResult aGist
                           let firstMatch filename = findOf (gistFiles <<< traversed) (\gistFile -> view gistFileFilename gistFile == filename) gist
                               playgroundGistFile = firstMatch gistSourceFilename
                               simulationGistFile = firstMatch gistSimulationFilename

                           -- Load the source, if available.
                           -- TODO There's a clearout happening here that should be in sync with other places.
                           -- TODO We should be saving to local storage, right?
                           case preview (_Just <<< gistFileContent <<< _Just) playgroundGistFile of
                             Nothing -> pure unit
                             Just content -> do void $ withEditor $ Editor.setValue content (Just 1)
                                                assign _simulation Nothing
                                                assign _evaluationResult NotAsked

                           -- Load the simulation, if available.
                           -- TODO There's a clearout happening here that should be in sync with other places.
                           case preview (_Just <<< gistFileContent <<< _Just) simulationGistFile of
                             Nothing -> pure unit
                             Just simulationString -> do
                               case (decodeJson =<< jsonParser simulationString) of
                                 Left err -> pure unit
                                 Right simulation -> do
                                                     assign _simulation $ Just simulation
                                                     assign _evaluationResult NotAsked

                         _ -> pure unit

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
  mContents <- getEditorContents

  case mContents of
    Nothing -> pure next
    Just contents -> do
      result <- runAjaxTo _compilationResult $ postContract contents

      -- If we got a successful result, switch tab.
      case result of
        Success (Left _) -> pure unit
        _ -> replaceViewOnSuccess result Editor Simulations

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
          oldSignatures <- use (_simulation <<< _Just <<< _Newtype <<< _signatures)
          unless (oldSignatures `gEq` newSignatures)
            (assign _simulation $ Just $ Simulation { signatures: newSignatures
                                                    , actions: []
                                                    , wallets: mkSimulatorWallet <$> 1..2
                                                    })
        _ -> pure unit

      pure next

eval (ScrollTo {row, column} next) = do
  void $ withEditor $ Editor.gotoLine row (Just column) (Just true)
  pure next

eval (ModifyActions actionEvent next) = do
  modifying (_simulation <<< _Just <<< _Newtype <<< _actions) (evalActionEvent actionEvent)
  pure next

eval (EvaluateActions next) = do
  _ <- runMaybeT $
       do evaluation <- MaybeT do
            contents <- getEditorContents
            simulation <- use _simulation
            pure $ join $ toEvaluation <$> contents <*> simulation

          result <- lift $ runAjaxTo  _evaluationResult $ postEvaluate evaluation

          replaceViewOnSuccess result Simulations Transactions

          lift updateChartsIfPossible

          pure unit
  pure next

eval (AddWallet next) = do
  modifying (_simulation <<< _Just <<< _Newtype <<< _wallets)
    (\wallets -> let maxWalletId = fromMaybe 0 $ maximumOf (traversed <<< _simulatorWalletWallet <<< _walletId) wallets
                     newWallet = mkSimulatorWallet (maxWalletId + 1)
                 in Array.snoc wallets newWallet)

  pure next

eval (RemoveWallet index next) = do
  modifying (_simulation <<< _Just <<< _Newtype <<< _wallets) (fromMaybe <*> Array.deleteAt index)
  assign (_simulation <<< _Just <<< _Newtype <<< _actions) []
  pure next

eval (SetBalance wallet newBalance next) = do
  modifying (_simulation <<< _Just <<< _Newtype <<< _wallets <<< traversed)
    (\simulatorWallet -> if view _simulatorWalletWallet simulatorWallet == wallet
                         then set _simulatorWalletBalance newBalance simulatorWallet
                         else simulatorWallet)
  pure next

eval (PopulateAction n l event) = do
  modifying
    (_simulation
       <<< _Just
       <<< _Newtype
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

getEditorContents :: forall m eff.
  MonadEff (ace :: ACE | eff) m
  => HalogenM State Query ChildQuery ChildSlot Void m (Maybe SourceCode)
getEditorContents = map SourceCode <$> (withEditor $ Editor.getValue)

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
        , row_
            [ col10_ [ mainTabBar state.view ]
            , col2_ [ gistControls
                        (view _authStatus state)
                        (view _createGistResult state)
                        (view _gistUrl state)
                    ]
            ]
        ]
    , viewContainer state.view Editor $
        [ editorPane state
        , case state.compilationResult of
            Failure error -> ajaxErrorPane error
            _ -> empty
        ]
    , viewContainer state.view Simulations $
        case state.simulation of
          Just simulation ->
            [ simulationPane
                simulation
                state.evaluationResult
            , case state.evaluationResult of
                Failure error -> ajaxErrorPane error
                _ -> empty
            ]
          Nothing ->
            [ text "Click the "
            , strong_ [ text "Editor" ]
            , text " tab above and compile a contract to get started."
            ]
    , viewContainer state.view Transactions $
        case state.evaluationResult of
          Success evaluation ->
            [ evaluationPane evaluation ]
          Failure error ->
            [ text "Your simulation has errors. Click the "
            , strong_ [ text "Simulation" ]
            , text " tab above to fix them and recompile."
            ]
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
           , Simulations /\ "Simulation"
           , Transactions /\ "Transactions"
           ]

    mkTab :: Tuple View String -> HTML p (Query Unit)
    mkTab (link /\ title) =
      navItem_ [
        a
          [ id_ $ "tab-" <> String.toLower (show link)
          , classes $ [ navLink ] <> activeClass
          , onClick $ const $ Just $ action $ ChangeView link
          ]
          [ text title ]
      ]
      where
        activeClass =
          if link == activeView
          then [ active ]
          else []
