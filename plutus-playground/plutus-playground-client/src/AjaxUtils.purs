module AjaxUtils where

import Bootstrap (alertDanger_)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (class MonadAsk, ReaderT, ask, runReaderT)
import Control.Monad.State (class MonadState)
import Control.MonadPlus ((=<<))
import Data.Argonaut.Generic.Aeson (decodeJson)
import Data.Argonaut.Parser (jsonParser)
import Data.Array (intercalate)
import Data.Either (Either(..))
import Data.Lens (Lens', assign)
import Halogen.HTML (HTML, br_, div_, pre_, text)
import Network.HTTP.StatusCode (StatusCode(..))
import Network.RemoteData (RemoteData(..), fromEither)
import Playground.API (CompilationError(..))
import Prelude (discard, bind, pure, show, ($), (<$>), (<>), (>>>))
import Servant.PureScript.Affjax (AjaxError, ErrorDescription(ConnectionError, DecodingError, ParsingError, UnexpectedHTTPStatus), runAjaxError)

showAjaxError :: forall p i. AjaxError -> HTML p i
showAjaxError =
  runAjaxError >>> _.description >>> showErrorDescription

showErrorDescription :: forall p i. ErrorDescription -> HTML p i
showErrorDescription (UnexpectedHTTPStatus {status, response}) =
  case status, response of
    (StatusCode 400), _ ->
      case (decodeJson =<< jsonParser response) :: Either String (Array CompilationError) of
        Left _ -> defaultError status
        Right compilationErrors ->
          div_ (showCompilationError <$> compilationErrors)
    _, _ ->  defaultError status
  where
    defaultError status =
      text $ "UnexpectedHTTPStatus: " <> response <> " " <> show status

    showCompilationError (RawError rawError) = text rawError
    showCompilationError (CompilationError error) = pre_ [ text $ intercalate "\n" error.text ]

showErrorDescription (ParsingError err) = text $ "ParsingError: " <> err
showErrorDescription (DecodingError err) = text $ "DecodingError: " <> err
showErrorDescription (ConnectionError err) = text $ "ConnectionError: " <> err

ajaxErrorPane :: forall p i. AjaxError -> HTML p i
ajaxErrorPane error =
  div_
    [ alertDanger_
        [ showAjaxError error
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


-- | Run an Ajax action, tracking its state and result into the target lens.
runAjaxTo :: forall m a e env state.
  MonadState state m
  => MonadAsk env m
  => Lens' state (RemoteData e a)
  -> ReaderT env (ExceptT e m) a -> m (RemoteData e a)
runAjaxTo lens action = do
  assign lens Loading
  result <- runAjax action
  assign lens result
  pure result
