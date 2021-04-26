module API.Request
  ( doPostRequest
  , doEmptyPostRequest
  , doGetRequest
  ) where

import Prelude
import Affjax (Request, Response, defaultRequest)
import Affjax.RequestBody (string)
import Control.Monad.Error.Class (class MonadError)
import Data.HTTP.Method (fromString)
import Data.Lens (Lens', view)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Effect.Aff.Class (class MonadAff)
import Foreign.Class (decode)
import Foreign.Generic (class Decode, class Encode, encodeJSON)
import Servant.PureScript.Ajax (AjaxError, ajax)

doPostRequest ::
  forall m d e.
  MonadError AjaxError m =>
  MonadAff m =>
  Decode d =>
  Encode e =>
  String -> e -> m d
doPostRequest url requestBody =
  perform
    $ defaultRequest
        { method = fromString "POST"
        , url = url
        , headers = defaultRequest.headers
        , content = Just $ string $ encodeJSON requestBody
        }

doEmptyPostRequest ::
  forall m d.
  MonadError AjaxError m =>
  MonadAff m =>
  Decode d =>
  String -> m d
doEmptyPostRequest url =
  perform
    $ defaultRequest
        { method = fromString "POST"
        , url = url
        , headers = defaultRequest.headers
        }

doGetRequest ::
  forall m d.
  MonadError AjaxError m =>
  MonadAff m =>
  Decode d =>
  String -> m d
doGetRequest url =
  perform
    $ defaultRequest
        { method = fromString "GET"
        , url = url
        , headers = defaultRequest.headers
        }

perform ::
  forall m d.
  MonadError AjaxError m =>
  MonadAff m =>
  Decode d =>
  Request Unit -> m d
perform request = map (view _body) (ajax decode request)
  where
  _body :: forall a. Lens' (Response a) a
  _body = prop (SProxy :: SProxy "body")
