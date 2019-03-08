module MainFrame
  ( mainFrame
  ) where

import Types

import API (SourceCode(SourceCode), _RunResult)
import API as API
import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceEffects, AceMessage(TextChanged), AceQuery(GetEditor))
import Ace.Types (ACE, Editor, Annotation)
import AjaxUtils (ajaxErrorPane, runAjaxTo)
import Analytics (Event, defaultEvent, trackEvent, ANALYTICS)
import Bootstrap (active, btn, btnGroup, btnSmall, container, container_, hidden, navItem_, navLink, navTabs_, pullRight)
import Control.Comonad (extract)
import Control.Monad.Aff.Class (class MonadAff, liftAff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Reader.Class (class MonadAsk)
import Control.Monad.State (class MonadState)
import Control.Monad.Trans.Class (lift)
import Data.Argonaut.Core (Json)
import Data.Argonaut.Core as Json
import Data.Array (catMaybes, (..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic (gEq)
import Data.Int as Int
import Data.Lens (_2, _Just, _Right, assign, maximumOf, modifying, over, preview, set, traversed, use, view)
import Data.Lens.Index (ix)
import Data.Map (Map)
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
import LocalStorage (LOCALSTORAGE)
import LocalStorage as LocalStorage
import Meadow (SPParams_, getOauthStatus, patchGistsByGistId, postGists)
import Meadow (postContractHaskell)
import Network.HTTP.Affjax (AJAX)
import Network.RemoteData (RemoteData(NotAsked, Loading, Failure, Success), _Success, isSuccess)
import Prelude (type (~>), Unit, Void, bind, const, discard, flip, map, pure, show, unit, unless, void, when, ($), (&&), (+), (-), (<$>), (<*>), (<<<), (<>), (==), (>>=))
import Servant.PureScript.Settings (SPSettings_)
import Simulation (simulationPane)
import StaticData (bufferLocalStorageKey, marloweBufferLocalStorageKey)
import StaticData as StaticData

examplePeople :: Map PersonId Person
examplePeople = Map.fromFoldable
                  [ Tuple (PersonId 1) 
                          { id: (PersonId 1)
                          , actions: [ Commit 1 2 3
                                     , Redeem 4 5
                                     ]
                          , suggestedActions: [ Choose 1 2
                                              , Claim 3 4
                                              ]
                          , signed: true
                          }
                  , Tuple (PersonId 2)
                          { id: (PersonId 2)
                          , actions: [ Choose 1 2
                                     , Claim 3 4
                                     ]
                          , suggestedActions: [ Commit 1 2 3
                                              , Claim 3 4
                                              ]
                          , signed: false
                          }
                  ]

initialState :: State
initialState =
  { view: Editor
  , runResult: NotAsked
  , marloweCompileResult: Right unit
  , authStatus: NotAsked
  , createGistResult: NotAsked
  , marloweState: { people: examplePeople, state: SimulationState 0 }
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
toEvent (MarloweHandleEditorMessage _ _) = Nothing
toEvent (MarloweHandleDragEvent _ _) = Nothing
toEvent (MarloweHandleDropEvent _ _) = Just $ defaultEvent "MarloweDropScript"
toEvent (CheckAuthStatus _) = Nothing
toEvent (PublishGist _) = Just $ (defaultEvent "Publish") { label = Just "Gist"}
toEvent (ChangeView view _) = Just $ (defaultEvent "View") { label = Just $ show view}
toEvent (LoadScript script a) = Just $ (defaultEvent "LoadScript") { label = Just script}
toEvent (LoadMarloweScript script a) = Just $ (defaultEvent "LoadMarloweScript") { label = Just script}
toEvent (CompileProgram a) = Just $ defaultEvent "CompileProgram"
toEvent (ScrollTo _ _) = Nothing
toEvent (UpdatePerson _ _) = Nothing
toEvent (ApplyTrasaction _) = Just $ defaultEvent "ApplyTransaction"
toEvent (NextBlock _) = Just $ defaultEvent "NextBlock"
toEvent (CompileMarlowe _) = Just $ defaultEvent "CompileMarlowe"

saveBuffer :: forall eff. String -> Eff (localStorage :: LOCALSTORAGE | eff) Unit
saveBuffer text = LocalStorage.setItem bufferLocalStorageKey text

saveMarloweBuffer :: forall eff. String -> Eff (localStorage :: LOCALSTORAGE | eff) Unit
saveMarloweBuffer text = LocalStorage.setItem marloweBufferLocalStorageKey text

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

eval (MarloweHandleEditorMessage (TextChanged text) next) = do
  liftEff $ saveMarloweBuffer text
  pure next

eval (MarloweHandleDragEvent event next) = do
  liftEff $ preventDefault event
  pure next

eval (MarloweHandleDropEvent event next) = do
  liftEff $ preventDefault event
  contents <- liftAff $ readFileFromDragEvent event
  void $ withMarloweEditor $ Editor.setValue contents (Just 1)
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
      assign _runResult NotAsked
      pure next

eval (LoadMarloweScript key next) = do
  case Map.lookup key StaticData.marloweContracts of
    Nothing -> pure next
    Just contents -> do
      void $ withMarloweEditor $ Editor.setValue contents (Just 1)
      pure next

eval (CompileProgram next) = do
  mContents <- withEditor Editor.getValue

  case mContents of
    Nothing -> pure next
    Just contents -> do
      result <- runAjaxTo _runResult $ postContractHaskell $ SourceCode contents

      -- Update the error display.
      void $ withEditor $ showCompilationErrorAnnotations $
        case result of
          Success (Left errors) -> errors
          _ -> []

      pure next

eval (ScrollTo {row, column} next) = do
  void $ withEditor $ Editor.gotoLine row (Just column) (Just true)
  pure next

eval (UpdatePerson person next) = do
  -- updating a person will require running the simulation so that the next suggested actions can be added
  -- although I'm not sure from the design what are suggested and what are manual
  currentState <- use _marloweState
  assign (_marloweState <<< _people) $ Map.update (const <<< Just $ person) person.id currentState.people
  pure next

eval (ApplyTrasaction next) = pure next

eval (NextBlock next) = do
  modifying (_marloweState <<< _state) (\(SimulationState block) -> SimulationState (block + 1))
  pure next

eval (CompileMarlowe next) = pure next

------------------------------------------------------------

-- | Handles the messy business of running an editor command if the
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

withMarloweEditor :: forall m eff a.
  MonadEff (ace :: ACE | eff) m
  => (Editor -> Eff (ace :: ACE | eff) a)
  -> HalogenM State Query ChildQuery ChildSlot Void m (Maybe a)
withMarloweEditor action = do
  mEditor <- H.query' cpMarloweEditor MarloweEditorSlot $ H.request GetEditor
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
        [ simulationPane state
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
        [ text "Meadow" ]
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
    tabs = [ Editor /\ "Haskell Editor"
           , Simulation /\ "Simulation"
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
