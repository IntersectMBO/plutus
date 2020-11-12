{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Auth
    ( API
    , FrontendAPI
    , server
    , AuthStatus
    , AuthRole
    , Config(..)
    , configJWTSignature
    , configRedirectUrl
    , configGithubClientId
    , configGithubClientSecret
    , GithubEndpoints
    , mkGithubEndpoints
    , githubEndpointsAuthLocation
    , githubEndpointsAccessTokenLocation
    , githubEndpointsApiBaseUrl
    , githubEndpointsCallbackUri
    ) where

import           Auth.Types                  (OAuthClientId, OAuthClientSecret, OAuthCode, OAuthToken, Token (Token),
                                              TokenProvider (Github), addUserAgent, oAuthTokenAccessToken)
import           Control.Lens                (_1, _2, makeLenses, view)
import           Control.Monad               (guard)
import           Control.Monad.Except        (MonadError)
import           Control.Monad.IO.Class      (MonadIO, liftIO)
import           Control.Monad.Logger        (MonadLogger, logDebugN, logErrorN)
import           Control.Monad.Now           (MonadNow, getCurrentTime, getPOSIXTime)
import           Control.Monad.Reader        (MonadReader)
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
import           Gist                        (Gist, GistId, NewGist)
import qualified Gist
import           Network.HTTP.Client.Conduit (getUri)
import           Network.HTTP.Conduit        (Request, parseRequest, responseBody, responseStatus, setQueryString)
import           Network.HTTP.Simple         (addRequestHeader)
import           Network.HTTP.Types          (hAccept, statusIsSuccessful)
import           Servant                     (Get, Header, Headers, JSON, NoContent (NoContent), QueryParam,
                                              ServerError, ServerT, StdMethod (GET), ToHttpApiData, Verb, addHeader,
                                              err401, err500, errBody, throwError, (:<|>) ((:<|>)), (:>))
import           Servant.API.BrowserHeader   (BrowserHeader)
import           Servant.Client              (BaseUrl, ClientM, mkClientEnv, parseBaseUrl, runClientM)
import           Web.Cookie                  (SetCookie, defaultSetCookie, parseCookies, setCookieExpires,
                                              setCookieHttpOnly, setCookieMaxAge, setCookieName, setCookiePath,
                                              setCookieSecure, setCookieValue)
import qualified Web.JWT                     as JWT

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
       :<|> (BrowserHeader "Cookie" Text :> "gists" :> Gist.GistAPI)

type CallbackAPI
     = "oauth" :> "github" :> "callback" :> QueryParam "code" OAuthCode :> GetRedirect (Headers '[ Header "Set-Cookie" SetCookie, Header "Location" Text])

------------------------------------------------------------
data AuthRole
    = Anonymous
    | GithubUser
    deriving (Show, Eq, Generic, FromJSON, ToJSON)

newtype AuthStatus =
    AuthStatus
        { _authStatusAuthRole :: AuthRole
        }
    deriving (Show, Eq, Generic, FromJSON, ToJSON)

data GithubEndpoints =
    GithubEndpoints
        { _githubEndpointsAuthLocation        :: !Request
        , _githubEndpointsAccessTokenLocation :: !Request
        , _githubEndpointsApiBaseUrl          :: !BaseUrl
        , _githubEndpointsCallbackUri         :: !Text
        }

makeLenses 'GithubEndpoints

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
data Config =
    Config
        { _configJWTSignature       :: !JWT.Signer
        , _configRedirectUrl        :: !Text
        , _configGithubClientId     :: !OAuthClientId
        , _configGithubClientSecret :: !OAuthClientSecret
        }

makeLenses 'Config

instance FromJSON Config where
    parseJSON =
        withObject "config" $ \o -> do
            _configGithubClientId <- o .: "github-client-id"
            _configGithubClientSecret <- o .: "github-client-secret"
            _configJWTSignature <- JWT.hmacSecret <$> o .: "jwt-signature"
            _configRedirectUrl <- o .: "redirect-url"
            pure Config {..}

type Env = (GithubEndpoints, Config)

------------------------------------------------------------
hSessionIdCookie :: Text
hSessionIdCookie = "sessionId"

-- | The JWT key we can lookup for the Github token's value.
githubTokenClaim :: Text
githubTokenClaim = "github-token"

------------------------------------------------------------
redirect ::
       ToHttpApiData loc
    => loc -- ^ what to put in the 'Location' header
    -> Headers '[ Header "Location" loc] NoContent
redirect a = addHeader a NoContent

githubRedirect ::
       (MonadLogger m, MonadReader Env m)
    => m (Headers '[ Header "Location" Text] NoContent)
githubRedirect = do
    logDebugN "Processing github redirect."
    _configRedirectUrl <- view (_2 . configRedirectUrl)
    _githubEndpointsCallbackUri <- view (_1 . githubEndpointsCallbackUri)
    _configGithubClientId <- view (_2 . configGithubClientId)
    _githubEndpointsAuthLocation <- view (_1 . githubEndpointsAuthLocation)
    let githubRedirectUrl =
            showText .
            getUri .
            setQueryString
                [ param "redirect_uri" $
                  _configRedirectUrl <> _githubEndpointsCallbackUri
                , param "scope" oauthScopes
                , param "client_id" (unpack _configGithubClientId)
                ] $
            _githubEndpointsAuthLocation
    logDebugN $ "Redirecting to: " <> showText githubRedirectUrl
    pure $ redirect githubRedirectUrl
  where
    oauthScopes = "gist"
    param key value = (key, Just $ encodeUtf8 value)

twoWeeks :: NominalDiffTime
twoWeeks = 60 * 60 * 24 * 7 * 2

expiryDuration :: NominalDiffTime
expiryDuration = twoWeeks

authStatus ::
       (MonadNow m, MonadLogger m, MonadReader Env m)
    => Maybe Text
    -> m AuthStatus
authStatus cookieHeader = do
    jwtSignature <- view (_2 . configJWTSignature)
    now <- getPOSIXTime
    _authStatusAuthRole <-
        case extractGithubToken jwtSignature now cookieHeader of
            Right _ -> do
              pure GithubUser
            Left err -> do
                logDebugN $
                    "Failed to extract github token at step: " <> showText err
                pure Anonymous
    let authStatusResult = AuthStatus {..}
    logDebugN $ "Authentication status is: " <> showText authStatusResult
    pure authStatusResult

extractGithubToken ::
       JWT.Signer -> POSIXTime -> Maybe Text -> Either Text (Token 'Github)
extractGithubToken signer now cookieHeader =
    runTrace "Reading cookies." $ do
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
            Map.lookup githubTokenClaim .
            JWT.unClaimsMap . JWT.unregisteredClaims $
            claims
        attempt $ "Extracting token as a string: " <> showText json
        withTrace $
            case json of
                String token -> pure $ Token token
                _            -> Nothing

githubCallback ::
       ( MonadLogger m
       , MonadWeb m
       , MonadError ServerError m
       , MonadNow m
       , MonadReader Env m
       )
    => Maybe OAuthCode
    -> m (Headers '[ Header "Set-Cookie" SetCookie, Header "Location" Text] NoContent)
githubCallback Nothing =
    withErr500 . pure . Left $
    "Expected a response from Github with an authorization code. Didn't get one!"
githubCallback (Just code) = do
    githubEndpoints <- view _1
    config@Config {..} <- view _2
    logDebugN "OAuth Code received. Swapping for a long-lived token."
    manager <- makeManager
    response <-
        withErr500 $
        doRequest manager $ makeTokenRequest githubEndpoints config code
    token <-
        withErr500 . pure . first Text.pack $
        if statusIsSuccessful (responseStatus response)
            then eitherDecode $ responseBody response
            else Left $ "Response: " <> show response
    now <- getCurrentTime
    let cookie = createSessionCookie _configJWTSignature token now
    logDebugN "Sending cookie."
    pure . addHeader cookie . addHeader _configRedirectUrl $ NoContent

withErr ::
       (MonadLogger m, MonadError ServerError m)
    => ServerError
    -> m (Either Text b)
    -> m b
withErr servantErr action =
    action >>= \case
        Left err -> do
            logErrorN err
            throwError $
                servantErr {errBody = LBS.fromStrict . encodeUtf8 $ err}
        Right r -> pure r

withErr500 ::
       (MonadLogger m, MonadError ServerError m) => m (Either Text b) -> m b
withErr500 = withErr err500

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
        , setCookieMaxAge = Just . fromRational . toRational $ expiryDuration
        , setCookieSecure = True
        , setCookieHttpOnly = True -- Not accessible from JavaScript
        }
  where
    expiryDate = addUTCTime expiryDuration now
    cookieValue = JWT.encodeSigned signer mempty jwtClaims
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
       ( MonadNow m
       , MonadLogger m
       , MonadWeb m
       , MonadError ServerError m
       , MonadIO m
       , MonadReader Env m
       )
    => Maybe Text
    -> m [Gist]
getGists header = withGithubToken header (\token -> Gist.getGists $ Just token)

createNewGist ::
       ( MonadNow m
       , MonadLogger m
       , MonadWeb m
       , MonadError ServerError m
       , MonadIO m
       , MonadReader Env m
       )
    => Maybe Text
    -> NewGist
    -> m Gist
createNewGist header newGist =
    withGithubToken header (\token -> Gist.createNewGist (Just token) newGist)

getGist ::
       ( MonadNow m
       , MonadLogger m
       , MonadWeb m
       , MonadError ServerError m
       , MonadIO m
       , MonadReader Env m
       )
    => Maybe Text
    -> GistId
    -> m Gist
getGist header gistId =
    withGithubToken header (\token -> Gist.getGist (Just token) gistId)

updateGist ::
       ( MonadNow m
       , MonadLogger m
       , MonadWeb m
       , MonadError ServerError m
       , MonadIO m
       , MonadReader Env m
       )
    => Maybe Text
    -> GistId
    -> NewGist
    -> m Gist
updateGist header gistId newGist =
    withGithubToken
        header
        (\token -> Gist.updateGist (Just token) gistId newGist)

withGithubToken ::
       ( MonadNow m
       , MonadLogger m
       , MonadError ServerError m
       , MonadWeb m
       , MonadIO m
       , MonadReader Env m
       )
    => Maybe Text
    -> (Token 'Github -> ClientM a)
    -> m a
withGithubToken cookieHeader action = do
    baseUrl <- view (_1 . githubEndpointsApiBaseUrl)
    jwtSignature <- view (_2 . configJWTSignature)
    logDebugN "Initialising connection manager."
    manager <- makeManager
    let clientEnv = mkClientEnv manager baseUrl
    now <- getPOSIXTime
    logDebugN "Extracting token."
    case extractGithubToken jwtSignature now cookieHeader of
        Left err -> do
            logErrorN $
                "Failed to extract github token at step: " <> showText err
            throwError err401
        Right token -> do
            logDebugN "Making github request with token."
            response <- liftIO $ flip runClientM clientEnv $ action token
            case response of
                Left err -> do
                    logErrorN $
                        "Failed to read github endpoint: " <> showText err
                    throwError err500
                Right result -> do
                  logDebugN "Github request successful."
                  pure result

server ::
       ( MonadNow m
       , MonadWeb m
       , MonadLogger m
       , MonadError ServerError m
       , MonadIO m
       , MonadReader Env m
       )
    => ServerT API m
server =
    ((authStatus :<|> githubRedirect) :<|>
     (\header ->
          getGists header :<|> createNewGist header :<|> getGist header :<|>
          updateGist header)) :<|>
    githubCallback

showText :: Show a => a -> Text
showText = Text.pack . show
