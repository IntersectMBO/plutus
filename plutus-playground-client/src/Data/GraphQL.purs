module Data.GraphQL where

import Prelude
import Affjax (defaultRequest) as Affjax
import Affjax.RequestBody (json) as Affjax
import Control.Monad.Error.Class (class MonadError)
import Data.Argonaut.Core (Json, jsonEmptyObject)
import Data.Argonaut.Encode (class EncodeJson, assoc, encodeJson, extend)
import Data.Either (Either)
import Data.Foldable (foldr)
import Data.HTTP.Method as Method
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error, try)
import Foreign (F, Foreign)
import Foreign.Index (ix)
import Servant.PureScript.Ajax (AjaxError, ajax)

newtype GraphQLQuery a
  = GraphQLQuery
  { operationName :: Maybe String
  , query :: String
  , variables :: Array (Tuple String Json)
  }

instance encodeJsonGraphQLQuery :: EncodeJson (GraphQLQuery a) where
  encodeJson (GraphQLQuery record) =
    jsonEmptyObject
      # extend (assoc "operationName" record.operationName)
      # extend (assoc "variables" (encodeJson (foldr extend jsonEmptyObject record.variables)))
      # extend (assoc "query" record.query)

runQuery ::
  forall m a.
  MonadError AjaxError m =>
  MonadAff m =>
  { baseURL :: String
  , query :: GraphQLQuery a
  } ->
  (Foreign -> F a) ->
  m a
runQuery {baseURL, query} decoder = do
  _.body
    <$> ajax (\obj -> ix obj "data" >>= decoder)
        ( Affjax.defaultRequest
          { method = Method.fromString "POST"
          , url = baseURL
          , content = Just $ Affjax.json $ encodeJson query
          }
        )

foreign import data GraphQLSchema :: Type

foreign import buildSchemaImpl :: String -> Effect GraphQLSchema

buildSchema :: String -> Effect (Either Error GraphQLSchema)
buildSchema str = try $ buildSchemaImpl str

foreign import buildClientSchemaImpl :: String -> Effect GraphQLSchema

buildClientSchema :: String -> Effect (GraphQLSchema)
buildClientSchema str = buildClientSchemaImpl str
