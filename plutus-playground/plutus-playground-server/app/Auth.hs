{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Auth
  ( API
  , FrontendAPI
  , server
  , AuthStatus
  , AuthRole
  , Config(..)
  , GithubEndpoints
  , mkGithubEndpoints
  ) where

import           Auth.Types                  (OAuthClientId, OAuthClientSecret, OAuthCode, OAuthToken, Token (Token),
                                              TokenProvider (Github), addUserAgent, oAuthTokenAccessToken)
import           Control.Monad               (guard)
import           Control.Monad.Except        (MonadError)
import           Control.Monad.IO.Class      (MonadIO, liftIO)
import           Control.Monad.Logger        (MonadLogger, logDebugN, logErrorN)
import           Control.Monad.Now           (MonadNow, getCurrentTime, getPOSIXTime)
import           Control.Monad.Trace         (attempt, runTrace, withTrace)
import           Control.Monad.Web           (MonadWeb, doRequest, makeManager)
import           Control.Newtype.Generics    (Newtype, O, unpack)
import           Data.Aeson                  (FromJSON, ToJSON, Value (String), eitherDecode, parseJSON, withObject,
                                              (.:))
import           Data.Bifunctor              (first)
import           Data.ByteString             (ByteString)
import qualified Data.ByteString.Lazy        as LBS
import qualified Data.Map                    as Map
import           Data.Text                   (Text)
import qualified Data.Text                   as Text
import           Data.Text.Encoding          (decodeUtf8, encodeUtf8)
import           Data.Time                   (NominalDiffTime, UTCTime, addUTCTime)
import           Data.Time.Clock.POSIX       (POSIXTime, utcTimeToPOSIXSeconds)
import           GHC.Generics                (Generic)
import           Gist                        (Gist)
import qualified Gist
import           Network.HTTP.Client         (managerModifyRequest)
import           Network.HTTP.Client.Conduit (getUri)
import           Network.HTTP.Client.TLS     (tlsManagerSettings)
import           Network.HTTP.Conduit        (Request, newManager, parseRequest, responseBody, responseStatus,
                                              setQueryString)
import           Network.HTTP.Simple         (addRequestHeader)
import           Network.HTTP.Types          (hAccept, statusIsSuccessful)
import           Servant                     ((:<|>) ((:<|>)), (:>), Get, Header, Headers, JSON, NoContent (NoContent),
                                              QueryParam, ServantErr, ServerT, StdMethod (GET), ToHttpApiData, Verb,
                                              addHeader, err401, err500, errBody, throwError)
import           Servant.API.BrowserHeader   (BrowserHeader)
import           Servant.Client              (BaseUrl, mkClientEnv, parseBaseUrl, runClientM)
import           Servant.Extra               ()
import           Web.Cookie                  (SetCookie, defaultSetCookie, parseCookies, setCookieExpires,
                                              setCookieHttpOnly, setCookieMaxAge, setCookieName, setCookiePath,
                                              setCookieSecure, setCookieValue)
import qualified Web.JWT                     as JWT

data AuthRole
  = Anonymous
  | GithubUser
  deriving (Show, Eq, Generic, FromJSON, ToJSON)

newtype AuthStatus = AuthStatus
  { _authStatusAuthRole :: AuthRole
  } deriving (Show, Eq, Generic, FromJSON, ToJSON)

-- | https://gist.github.com/alpmestan/757094ecf9401f85c5ba367ca20b8900
type GetRedirect headers = Verb 'GET 302 '[ JSON] (headers NoContent)

-- | We split out the API here because we don't want the Github
-- Callback to be exported for the frontend to call directly.
type API
   = FrontendAPI
     :<|> CallbackAPI

type FrontendAPI
   = ("oauth" :> (BrowserHeader "Cookie" Text :> "status" :> Get '[ JSON] AuthStatus
                  :<|> "github" :> GetRedirect (Headers '[ Header "Location" Text])))
     :<|> (BrowserHeader "Cookie" Text :> "gists" :> Get '[ JSON] [Gist])

type CallbackAPI
   = "oauth" :> "github" :> "callback" :> QueryParam "code" OAuthCode :> GetRedirect (Headers '[ Header "Set-Cookie" SetCookie, Header "Location" Text])

data GithubEndpoints = GithubEndpoints
  { _githubEndpointsAuthLocation        :: !Request
  , _githubEndpointsAccessTokenLocation :: !Request
  , _githubEndpointsApiBaseUrl          :: !BaseUrl
  , _githubEndpointsCallbackUri         :: !Text
  }

-- | Config determined by Github.
mkGithubEndpoints :: IO GithubEndpoints
mkGithubEndpoints = do
  _githubEndpointsAuthLocation <-
    parseRequest "GET https://github.com/login/oauth/authorize"
  _githubEndpointsAccessTokenLocation <-
    parseRequest "POST https://github.com/login/oauth/access_token"
  _githubEndpointsApiBaseUrl <- parseBaseUrl "https://api.github.com"
  let _githubEndpointsCallbackUri = "/api/oauth/github/callback"
  pure GithubEndpoints {..}

-- | Config supplied at runtime.
data Config = Config
  { _configJWTSignature       :: !JWT.Signer
  , _configRedirectUrl        :: !Text
  , _configGithubClientId     :: !OAuthClientId
  , _configGithubClientSecret :: !OAuthClientSecret
  }

instance FromJSON Config where
  parseJSON =
    withObject "config" $ \o -> do
      _configGithubClientId <- o .: "github-client-id"
      _configGithubClientSecret <- o .: "github-client-secret"
      _configJWTSignature <- JWT.hmacSecret <$> o .: "jwt-signature"
      _configRedirectUrl <- o .: "redirect-url"
      pure Config {..}

hSessionIdCookie :: Text
hSessionIdCookie = "sessionId"

-- | The JWT key we can lookup for the Github token's value.
githubTokenClaim :: Text
githubTokenClaim = "github-token"

redirect ::
     ToHttpApiData loc
  => loc -- ^ what to put in the 'Location' header
  -> Headers '[ Header "Location" loc] NoContent
redirect a = addHeader a NoContent

githubRedirect ::
     GithubEndpoints -> Config -> Headers '[ Header "Location" Text] NoContent
githubRedirect GithubEndpoints {..} Config {..} = redirect githubRedirectUrl
  where
    oauthScopes = "gist"
    githubRedirectUrl :: Text
    githubRedirectUrl =
      showText .
      getUri .
      setQueryString
        [ param "redirect_uri" $
          _configRedirectUrl <> _githubEndpointsCallbackUri
        , param "scope" oauthScopes
        , param "client_id" (unpack _configGithubClientId)
        ] $
      _githubEndpointsAuthLocation
    param key value = (key, Just $ encodeUtf8 value)

twoWeeks :: NominalDiffTime
twoWeeks = 60 * 60 * 24 * 7 * 2

authStatus ::
     (MonadNow m, MonadLogger m) => Config -> Maybe Text -> m AuthStatus
authStatus Config {..} cookieHeader = do
  now <- getPOSIXTime
  _authStatusAuthRole <-
    case extractGithubToken _configJWTSignature now cookieHeader of
      Right _ -> pure GithubUser
      Left err -> do
        logErrorN $ "Failed to extract github token at step: " <> showText err
        pure Anonymous
  pure AuthStatus {..}

extractGithubToken ::
     JWT.Signer -> POSIXTime -> Maybe Text -> Either Text (Token 'Github)
extractGithubToken signer now cookieHeader =
  runTrace $ do
    attempt "Reading cookies."
    cookies <- parseCookies . encodeUtf8 <$> withTrace cookieHeader
    attempt $ "Looking for Session ID cookie: " <> showText cookies
    githubAuth <- withTrace $ lookup (encodeUtf8 hSessionIdCookie) cookies
    attempt $ "Reading JWT Cookie: " <> decodeUtf8 githubAuth
    unverifiedJwt <- withTrace . JWT.decode . decodeUtf8 $ githubAuth
    attempt "Verifying JWT Cookie."
    verifiedJwt <- withTrace $ JWT.verify signer unverifiedJwt
    let claims = JWT.claims verifiedJwt
    attempt "Checking expiry date is set."
    expiry <- withTrace $ JWT.exp claims
    attempt "Checking expiry date is valid."
    guard (JWT.secondsSinceEpoch expiry > now)
    attempt "Looking for Github token claim."
    json <-
      withTrace .
      Map.lookup githubTokenClaim . JWT.unClaimsMap . JWT.unregisteredClaims $
      claims
    attempt $ "Extracting token as a string:" <> showText json
    withTrace $
      case json of
        String token -> pure $ Token token
        _            -> Nothing

githubCallback ::
     (MonadLogger m, MonadWeb m, MonadError ServantErr m, MonadNow m)
  => GithubEndpoints
  -> Config
  -> Maybe OAuthCode
  -> m (Headers '[ Header "Set-Cookie" SetCookie, Header "Location" Text] NoContent)
githubCallback _ _ Nothing =
  with500Err . pure . Left $
  "Expected a response from Github with an authorization code. Didn't get one!"
githubCallback githubEndpoints config@Config {..} (Just code) = do
  logDebugN "OAuth Code received. Swapping for a long-lived token."
  manager <- makeManager
  let tokenRequest = makeTokenRequest githubEndpoints config code
  response <- with500Err $ doRequest tokenRequest manager
  token <-
    with500Err $
    pure $
    first Text.pack $
    if statusIsSuccessful (responseStatus response)
      then eitherDecode $ responseBody response
      else Left $ "Response: " <> show response
  now <- getCurrentTime
  let cookie = createSessionCookie _configJWTSignature token now
  logDebugN "Sending cookie."
  pure . addHeader cookie . addHeader _configRedirectUrl $ NoContent

with500Err ::
     (MonadLogger m, MonadError ServantErr m) => m (Either Text b) -> m b
with500Err action =
  action >>= \case
    Left err -> do
      logErrorN err
      throwError $ err500 {errBody = LBS.fromStrict . encodeUtf8 $ err}
    Right r -> pure r

makeTokenRequest :: GithubEndpoints -> Config -> OAuthCode -> Request
makeTokenRequest GithubEndpoints {..} Config {..} code =
  setQueryString params .
  addUserAgent . addRequestHeader hAccept "application/json" $
  _githubEndpointsAccessTokenLocation
  where
    params =
      [ ("client_id", param _configGithubClientId)
      , ("client_secret", param _configGithubClientSecret)
      , ("code", param code)
      ]
    param ::
         forall a. (Newtype a, O a ~ Text)
      => a
      -> Maybe ByteString
    param = Just . encodeUtf8 . unpack

createSessionCookie :: JWT.Signer -> OAuthToken 'Github -> UTCTime -> SetCookie
createSessionCookie signer token now =
  defaultSetCookie
    { setCookieName = encodeUtf8 hSessionIdCookie
    , setCookieValue = encodeUtf8 cookieValue
    , setCookiePath = Just "/"
    , setCookieExpires = Just expiryDate
    , setCookieMaxAge = Just . fromRational . toRational $ twoWeeks
    , setCookieSecure = True
    , setCookieHttpOnly = True -- Not accessible from JavaScript
    }
  where
    expiryDate = addUTCTime twoWeeks now
    cookieValue = JWT.encodeSigned signer jwtClaims
    jwtClaims =
      mempty
        { JWT.exp = JWT.numericDate $ utcTimeToPOSIXSeconds expiryDate
        , JWT.unregisteredClaims =
            JWT.ClaimsMap $
            Map.fromList
              [ ( githubTokenClaim
                , String . unpack $ oAuthTokenAccessToken token)
              ]
        }

getGists ::
     (MonadNow m, MonadLogger m, MonadIO m, MonadError ServantErr m)
  => GithubEndpoints
  -> Config
  -> Maybe Text
  -> m [Gist]
getGists GithubEndpoints {..} Config {..} cookieHeader = do
  manager <-
    liftIO $
    newManager $ tlsManagerSettings {managerModifyRequest = pure . addUserAgent}
  let clientEnv = mkClientEnv manager _githubEndpointsApiBaseUrl
  now <- getPOSIXTime
  case extractGithubToken _configJWTSignature now cookieHeader of
    Left err -> do
      logErrorN $ "Failed to extract github token at step: " <> showText err
      throwError err401
    Right token -> do
      response <- liftIO (runClientM (Gist.getGists (Just token)) clientEnv)
      logDebugN $ "Gist response: " <> showText response
      case response of
        Left err -> do
          logErrorN $ "Failed to read github endpoint: " <> showText err
          throwError err500
        Right gists -> pure gists

server ::
     (MonadNow m, MonadWeb m, MonadLogger m, MonadError ServantErr m, MonadIO m)
  => GithubEndpoints
  -> Config
  -> ServerT API m
server githubEndpoints config =
  ((authStatus config :<|> pure (githubRedirect githubEndpoints config)) :<|>
   getGists githubEndpoints config) :<|>
  githubCallback githubEndpoints config

showText :: Show a => a -> Text
showText = Text.pack . show
