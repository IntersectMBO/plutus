module MonadApp where

import Prelude

import Ace (Annotation, Editor)
import Ace.EditSession as Session
import Ace.Editor as AceEditor
import Auth (AuthStatus)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Except.Trans (ExceptT, runExceptT)
import Control.Monad.Reader.Class (class MonadAsk)
import Control.Monad.State.Class (class MonadState)
import Control.Monad.Trans.Class (class MonadTrans, lift)
import Data.Argonaut.Encode ((:=))
import Data.GraphQL (GraphQLQuery(..))
import Data.GraphQL as GraphQL
import Data.Maybe (Maybe(..))
import Data.MediaType (MediaType)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.RawJson (JsonEither)
import Editor as Editor
import Debug.Trace (spy)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import FileEvents as FileEvents
import Foreign.Class (decode)
import Foreign.Index (ix)
import Gist (Gist, GistId, NewGist)
import Halogen (HalogenM)
import Language.Haskell.Interpreter (InterpreterError, SourceCode(SourceCode), InterpreterResult)
import LocalStorage as LocalStorage
import Network.RemoteData as RemoteData
import Playground.API (CompilationResult, Evaluation, EvaluationResult)
import Playground.Server (SPParams_)
import Playground.Server as Server
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import StaticData (bufferLocalStorageKey)
import Types (ChildQuery, ChildSlot, Country, EditorSlot(..), Greeting, Query, State, WebData, cpEditor)
import Web.HTML.Event.DataTransfer (DropEffect)
import Web.HTML.Event.DataTransfer as DataTransfer
import Web.HTML.Event.DragEvent (DragEvent, dataTransfer)

class Monad m <= MonadApp m where
  editorGetContents :: m (Maybe SourceCode)
  editorSetContents :: String -> Maybe Int -> m Unit
  editorSetAnnotations :: Array Annotation -> m Unit
  editorGotoLine :: Int -> Maybe Int -> m Unit
  --
  saveBuffer :: String -> m Unit
  preventDefault :: DragEvent -> m Unit
  setDropEffect :: DropEffect -> DragEvent -> m Unit
  setDataTransferData :: DragEvent -> MediaType -> String -> m Unit
  readFileFromDragEvent :: DragEvent -> m String
  --
  getOauthStatus :: m (WebData AuthStatus)
  getCountryByCode :: String -> m (WebData Country)
  getGreeting :: String -> m (WebData Greeting)
  getGistByGistId :: GistId -> m (WebData Gist)
  postEvaluation :: Evaluation -> m (WebData EvaluationResult)
  postGist :: NewGist -> m (WebData Gist)
  patchGistByGistId :: NewGist -> GistId -> m (WebData Gist)
  postContract :: SourceCode -> m (WebData (JsonEither InterpreterError (InterpreterResult CompilationResult)))

newtype HalogenApp m a = HalogenApp (HalogenM State Query ChildQuery ChildSlot Void m a)

derive instance newtypeHalogenApp :: Newtype (HalogenApp m a) _

derive newtype instance functorHalogenApp :: Functor (HalogenApp m)
derive newtype instance applicativeHalogenApp :: Applicative (HalogenApp m)
derive newtype instance applyHalogenApp :: Apply (HalogenApp m)
derive newtype instance bindHalogenApp :: Bind (HalogenApp m)
derive newtype instance monadHalogenApp :: Monad (HalogenApp m)
derive newtype instance monadTransHalogenApp :: MonadTrans HalogenApp
derive newtype instance monadStateHalogenApp :: MonadState State (HalogenApp m)
derive newtype instance monadAskHalogenApp :: MonadAsk env m => MonadAsk env (HalogenApp m)

instance monadThrowHalogenApp :: MonadThrow e m => MonadThrow e (HalogenApp m) where
  throwError e = lift (throwError e)

------------------------------------------------------------

runHalogenApp :: forall m a. HalogenApp m a -> HalogenM State Query ChildQuery ChildSlot Void m a
runHalogenApp = unwrap

instance monadAppHalogenApp ::
  ( MonadAsk (SPSettings_ SPParams_) m
  , MonadEffect m
  , MonadAff m
  )
  => MonadApp (HalogenApp m) where
  editorGetContents = map SourceCode <$> withEditor AceEditor.getValue
  editorSetContents contents cursor = void $ withEditor $ AceEditor.setValue contents cursor

  editorSetAnnotations annotations = void $ withEditor \editor -> do
      session <- AceEditor.getSession editor
      Session.setAnnotations annotations session

  editorGotoLine row column = void $ withEditor $ AceEditor.gotoLine row column (Just true)

  preventDefault event = wrap $ liftEffect $ FileEvents.preventDefault event

  setDropEffect dropEffect event = wrap $ liftEffect $ DataTransfer.setDropEffect dropEffect $ dataTransfer event
  setDataTransferData event mimeType value =
    wrap $ liftEffect $ DataTransfer.setData mimeType value $ dataTransfer event

  readFileFromDragEvent event = wrap $ liftAff $ FileEvents.readFileFromDragEvent event

  saveBuffer text = wrap $ liftEffect $ LocalStorage.setItem bufferLocalStorageKey text

  getOauthStatus = runAjax Server.getOauthStatus
  getGistByGistId gistId = runAjax $ Server.getGistsByGistId gistId
  postEvaluation evaluation = runAjax $ Server.postEvaluate evaluation
  postGist newGist = runAjax $ Server.postGists newGist
  patchGistByGistId newGist gistId = runAjax $ Server.patchGistsByGistId newGist gistId
  postContract source = runAjax $ Server.postContract source

  getCountryByCode code = wrap $ liftAff $ RemoteData.fromEither <$>
    runExceptT (GraphQL.runQuery
                  { baseURL: "https://countries.trevorblades.com/"
                  , query: countryQuery code
                  }
                  (\obj -> ix obj "country" >>= decode))

  getGreeting userName = wrap $ liftAff $ RemoteData.fromEither <$>
    runExceptT (GraphQL.runQuery
                  { baseURL: "/api/graphql"
                  , query: greetingQuery userName
                  }
                  decode)

schemadoc :: String
schemadoc = """
  type SourceCode {
    text: String
  }

  type TxId {
    id: String!
  }

  type FunctionSchema {
    name: String!
    schema: String!
  }

  type Tx {
    txInputs: [TxId!]!
    txOutputs: [TxId!]!
  }

  type Transaction {
    txId: TxId!
    tx: Tx!
  }

  type EvaluationResult {
    resultBlockchain: [[Transaction!]!]!
  }

  type TokenName {
    name: String!
  }

  type KnownCurrency {
    hash: String!
    friendlyName: String!
    knownTokens: [TokenName!]!
  }

  type CompilationResult {
    functionSchema: [FunctionSchema]!
    knownCurrencies: [KnownCurrency!]!
  }

  # the schema allows the following query:
  type Query {
  }

  this schema allows the following mutation:
  type Mutation {
    compile(source: SourceCode!): EvaluationResult
    evaluate(source: SourceCode!): CompilationResult
  }
"""


runAjax :: forall m a.
  ExceptT AjaxError (HalogenM State Query ChildQuery ChildSlot Void m) a
  -> HalogenApp m (WebData a)
runAjax action = wrap $ RemoteData.fromEither <$> runExceptT action

withEditor :: forall a m. MonadEffect m => (Editor -> Effect a) -> HalogenApp m (Maybe a)
withEditor = HalogenApp <<< Editor.withEditor cpEditor EditorSlot

countryQuery :: String -> GraphQLQuery Country
countryQuery code =
  GraphQLQuery
    { operationName: Just "CountryQuery"
    , query
    , variables: [ "code" := code ]
    }
  where
    query = """
      query CountryQuery ($code: String!) {
        country(code: $code) {
          name
          emoji
          currency
          languages {
            code
            name
          }
        }
      }
    """

greetingQuery :: String -> GraphQLQuery Greeting
greetingQuery userName =
  GraphQLQuery
    { operationName: Just "GreetingQuery"
    , query
    , variables: [ "userName" := userName
                 , "userAge" := 30
                 ]
    }
  where
    query = """
      query GreetingQuery ($userName: String!, $userAge: Int!) {
        greeting(userName: $userName, userAge: $userAge)
      }
    """
