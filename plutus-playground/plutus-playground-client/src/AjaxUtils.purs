module AjaxUtils where

import Bootstrap (alertDanger_)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (class MonadAsk, ReaderT, ask, runReaderT)
import Halogen (HTML)
import Halogen.HTML (br_, div_, text)
import Network.RemoteData (RemoteData, fromEither)
import Prelude (bind, pure, show, ($), (<>), (>>>))
import Servant.PureScript.Affjax (AjaxError, ErrorDescription(ConnectionError, DecodingError, ParsingError, UnexpectedHTTPStatus), runAjaxError)

showAjaxError :: AjaxError -> String
showAjaxError =
  runAjaxError >>> _.description >>> showErrorDescription

showErrorDescription :: ErrorDescription -> String
showErrorDescription (UnexpectedHTTPStatus {status, response}) = "UnexpectedHTTPStatus: " <> response <> " " <> show status
showErrorDescription (ParsingError err) = "ParsingError: " <> err
showErrorDescription (DecodingError err) = "DecodingError: " <> err
showErrorDescription (ConnectionError err) = "ConnectionError: " <> err

ajaxErrorPane :: forall p i. AjaxError -> HTML p i
ajaxErrorPane error =
  div_
    [ alertDanger_
        [ text $ showAjaxError error
        , br_
        , text "Please try again or contact support for assistance."
        ]
    ]

runAjax ::
  forall m env a e.
  MonadAsk env m
  => ReaderT env (ExceptT e m) a -> m (RemoteData e a)
runAjax action = do
  settings <- ask
  result <- runExceptT $ runReaderT action settings
  pure $ fromEither result
