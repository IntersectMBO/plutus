module AjaxUtils where

import Bootstrap (alertDanger_)
import Control.Monad.Reader.Class (class MonadAsk, ask)
import Control.MonadPlus ((=<<))
import Data.Argonaut.Core (Json)
import Data.Argonaut.Generic.Aeson (decodeJson)
import Data.Argonaut.Parser (jsonParser)
import Data.Array (intercalate)
import Data.Either (Either(..))
import Data.Generic (class Generic)
import Halogen.HTML (HTML, br_, div_, pre_, text)
import Language.Haskell.Interpreter (CompilationError(..))
import Network.HTTP.StatusCode (StatusCode(..))
import Prelude (bind, pure, show, ($), (<$>), (<>), (>>>))
import Servant.PureScript.Affjax (AjaxError, ErrorDescription(ConnectionError, DecodingError, ParsingError, UnexpectedHTTPStatus), runAjaxError)
import Servant.PureScript.Settings (SPSettingsDecodeJson_(..), SPSettingsEncodeJson_(..), SPSettings_(..))

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

getEncodeJson :: forall m params a. MonadAsk (SPSettings_ params) m => Generic a => m (a -> Json)
getEncodeJson = do
  SPSettings_ {encodeJson: (SPSettingsEncodeJson_ encodeJson)} <- ask
  pure encodeJson

getDecodeJson :: forall m params a. MonadAsk (SPSettings_ params) m => Generic a => m (Json -> Either String a)
getDecodeJson = do
  SPSettings_ {decodeJson: (SPSettingsDecodeJson_ decodeJson)} <- ask
  pure decodeJson
