module AjaxUtils where

import Bootstrap (alertDanger_)
import Control.Alt ((<|>))
import Control.Monad.Except.Trans (ExceptT(ExceptT), runExceptT)
import Control.MonadPlus (empty, (=<<))
import Data.Argonaut.Core (Json)
import Data.Argonaut.Generic.Aeson as Aeson
import Data.Argonaut.Generic.Decode (genericDecodeJson)
import Data.Argonaut.Generic.Options (Options(..))
import Data.Argonaut.Parser (jsonParser)
import Data.Array (intercalate)
import Data.Either (Either(Right, Left), note)
import Data.Generic (class Generic, GenericSignature(SigProd), GenericSpine(SProd), fromSpine, isValidSpine, toSignature, toSpine)
import Data.List as List
import Data.List.NonEmpty as NonEmpty
import Data.Maybe (Maybe(..), fromMaybe)
import Gist (GistId)
import Halogen.HTML (HTML, br_, div_, pre_, text)
import Language.Haskell.Interpreter (CompilationError(..))
import Network.HTTP.StatusCode (StatusCode(..))
import Playground.API (TokenId)
import Playground.Server (SPParams_(..))
import Prelude (bind, pure, show, unit, ($), (<$>), (<>), (>>>))
import Servant.PureScript.Affjax (AjaxError, ErrorDescription(ConnectionError, DecodingError, ParsingError, UnexpectedHTTPStatus), runAjaxError)
import Servant.PureScript.Settings (SPSettingsDecodeJson_(..), SPSettingsEncodeJson_(..), SPSettingsToUrlPiece_(..), SPSettings_(..), URLPiece, defaultSettings, gDefaultToURLPiece)
import Type.Proxy (Proxy(..))

ajaxSettings :: SPSettings_ SPParams_
ajaxSettings = SPSettings_ $ settings
  { toURLPiece = SPSettingsToUrlPiece_ gCustomToURLPiece
  , decodeJson = SPSettingsDecodeJson_ (genericDecodeJson $ Options $ options {userDecoding = userDecoding})
  }
  where
    SPSettings_ settings = defaultSettings $ SPParams_ { baseURL: "/api/" }
    Options options = Aeson.options

decodeJson :: forall a. Generic a => Json -> Either String a
decodeJson =
  let (SPSettings_ {decodeJson: SPSettingsDecodeJson_ decoder}) = ajaxSettings
  in decoder

encodeJson :: forall a. Generic a => a -> Json
encodeJson =
  let (SPSettings_ {encodeJson: SPSettingsEncodeJson_ encoder}) = ajaxSettings
  in encoder

userDecoding :: Options -> GenericSignature -> Json -> Maybe (Either String GenericSpine)
userDecoding opts sig json =
  decodeTokenIdLists opts sig json
  <|>
  Aeson.userDecoding opts sig json

decodeTokenIdLists :: Options -> GenericSignature -> Json -> Maybe (Either String GenericSpine)
decodeTokenIdLists opts sig@(SigProd "Data.List.Types.List" [{sigValues: [a, _]}, _]) json =
  runExceptT do
    case a unit of
      (SigProd "Playground.API.TokenId" _) -> do
        tokenIds :: Array TokenId <- ExceptT $ Just $ decodeJson json
        pure $ toSpine $ List.fromFoldable tokenIds
      _ -> empty
decodeTokenIdLists opts (SigProd "Data.List.Types.NonEmptyList" [{sigValues: [l]}]) json =
  runExceptT do
    case l unit of
      (SigProd "Data.List.Types.List" [{sigValues: [a, _]}, _])  -> do
        case a unit of
          (SigProd "Playground.API.TokenId" _) -> do
            tokenIds :: Array TokenId <- ExceptT $ Just $ decodeJson json
            nonEmpty <- ExceptT $ Just $ note "List is empty, expecting non-empty" $ NonEmpty.fromFoldable tokenIds
            pure $ toSpine nonEmpty
          _ -> empty
      _ -> empty
decodeTokenIdLists _ _ _ = Nothing

-- | Generally we want the default parameter encoding behaviour. But
-- sometimes we need to do something special.
gCustomToURLPiece :: forall a. Generic a => a -> URLPiece
gCustomToURLPiece v =
  fromMaybe (gDefaultToURLPiece v) $
  case toSpine v of
    SProd name [arg] ->
      if isInstanceOf (Proxy :: Proxy GistId) v
      then fromSpine $ arg unit
      else Nothing
    _ -> Nothing

isInstanceOf :: forall a b. Generic a => Generic b => Proxy a -> b -> Boolean
isInstanceOf proxy value =
  isValidSpine (toSignature proxy) (toSpine value)

showAjaxError :: forall p i. AjaxError -> HTML p i
showAjaxError =
  runAjaxError >>> _.description >>> showErrorDescription

showErrorDescription :: forall p i. ErrorDescription -> HTML p i
showErrorDescription (UnexpectedHTTPStatus {status, response}) =
  case status, response of
    (StatusCode 400), _ ->
      case (decodeJson =<< jsonParser response) :: Either String (Array CompilationError) of
        Left _ -> defaultError
        Right compilationErrors ->
          div_ (showCompilationError <$> compilationErrors)
    _, _ ->  defaultError
  where
    defaultError =
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
