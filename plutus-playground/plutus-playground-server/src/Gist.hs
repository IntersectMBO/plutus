{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Gist
  ( main
  , Owner(..)
  , Gist(..)
  , GistFile(..)
  , Error(..)
  , getGists
  , k
  ) where

import           Control.Monad.Except   (MonadError, runExceptT, throwError)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Control.Monad.Logger   (MonadLogger, logInfoN, runStdoutLoggingT)
import           Control.Monad.Reader   (MonadReader, asks, runReaderT)
import           Data.Aeson             (FromJSON, ToJSON, eitherDecode, parseJSON, withObject, (.:))
import           Data.Aeson.Types       (Parser)
import qualified Data.ByteString.Char8  as BS
import           Data.Map               (Map)
import qualified Data.Map               as Map
import           Data.Proxy             (Proxy (Proxy))
import           Data.Text              (Text)
import qualified Data.Text              as Text
import           Data.Text.Encoding     (encodeUtf8)
import           Data.Yaml              (ParseException, decodeFileEither)
import           GHC.Generics           (Generic)
import           Network.HTTP.Conduit   (Request, parseRequest_, responseBody, setQueryString)
import           Network.HTTP.Simple    (addRequestHeader)
import           Network.HTTP.Types     (hAccept, hUserAgent)
import           Servant.API            ((:>), Get, Header, JSON)
import           Servant.Client         (ClientM, client)
import           Utils                  (MonadOAuth, MonadWeb, Token, TokenProvider (Github), defaultParseJSON,addUserAgent,
                                         doRequest, logDebugT, logInfoT, makeManager, sign, withError)
import           Web.Authenticate.OAuth (Credential, OAuth, newCredential, newOAuth, oauthAccessTokenUri,
                                         oauthConsumerKey, oauthConsumerSecret, oauthRequestUri, oauthServerName)

------------------------------------------------------------
-- | OAuth flow:
-- 1. Endpoint use can visit which redirects them to github.
-- 2. Callback endpoint that supplies a code. That endpoint:
--     a. Issues a request to turn the code into a token.
--     b. Encodes the token as JWT.
--     c. Redirects the user back to the app.
-- 3. Status endpoint, so we can see if we're logged in.
------------------------------------------------------------
data Config = Config
  { consumerKey       :: Text
  , consumerSecret    :: Text
  , accessToken       :: Text
  , accessTokenSecret :: Text
  } deriving (Show, Eq, Generic, FromJSON)

loadConfig :: (MonadIO m, MonadLogger m, MonadError Error m) => m Config
loadConfig = do
  let configFile = "playground.yaml"
  logInfoT $ "Reading config: " <> configFile
  decoded <- liftIO $ decodeFileEither configFile
  withError ReadConfigError decoded

type API
   = Header "Authorization" (Token 'Github) :> "gists" :> Get '[ JSON] [Gist]

getGists :: Maybe (Token 'Github) -> ClientM [Gist]
getGists = client (Proxy @API)

data Error
  = ReadConfigError ParseException
  | HttpError Text
  | DecodeJSONError String
  deriving (Show)

------------------------------------------------------------
githubCredentials :: Config -> Credential
githubCredentials =
  newCredential <$> encodeUtf8 . accessToken <*> encodeUtf8 . accessTokenSecret

githubOAuth :: Config -> OAuth
githubOAuth config =
  newOAuth
    { oauthConsumerKey = encodeUtf8 $ consumerKey config
    , oauthConsumerSecret = encodeUtf8 $ consumerSecret config
    , oauthServerName = "https://dev.twitter.com"
    , oauthRequestUri = "https://dev.twitter.com/oauth/request_token"
    , oauthAccessTokenUri = "https://dev.twitter.com/oauth2/token"
    }

------------------------------------------------------------
signRequest ::
     (MonadOAuth m, MonadReader Config m, MonadLogger m) => Request -> m Request
signRequest request = do
  oAuth <- asks githubOAuth
  credentials <- asks githubCredentials
  signedRequest <- sign oAuth credentials request
  logDebugT . show $ signedRequest
  return signedRequest

makeTimelineRequest ::
     (MonadOAuth m, MonadReader Config m, MonadLogger m) => Int -> m Request
makeTimelineRequest count =
  signRequest .
  setQueryString params .
  addUserAgent . addGithubApiHeader $
  parseRequest_
    "GET https://api.github.com/gists/439209ad6773b40b82b95b0048737333"
  where
    params = [("count", param count)]
    param :: Show a => a -> Maybe BS.ByteString
    param = Just . BS.pack . show

addGithubApiHeader :: Request -> Request
addGithubApiHeader = addRequestHeader hAccept "application/vnd.github.v3+json"

fetchTimeline ::
     ( MonadWeb m
     , MonadOAuth m
     , MonadIO m
     , MonadReader Config m
     , MonadError Error m
     , MonadLogger m
     )
  => m Gist
fetchTimeline = do
  signedRequest <- makeTimelineRequest 5
  manager <- makeManager
  response <- doRequest signedRequest manager
  case response of
    Left err -> throwError $ HttpError err
    Right r  -> withError DecodeJSONError $ eitherDecode $ responseBody r

data Owner = Owner
  { _ownerLogin   :: Text
  , _ownerHtmlUrl :: Text
  } deriving (Show, Eq, Generic, ToJSON)

data Gist = Gist
  { _gistGitPushUrl :: Text
  , _gistOwner      :: Owner
  , _gistFiles      :: [GistFile]
  , _gistTruncated  :: Bool
  } deriving (Show, Eq, Generic, ToJSON)

data GistFile = GistFile
  { _gistFilename :: Text
  , _gistLanguage :: Maybe Text
  , _gistType     :: Text
  } deriving (Show, Eq, Generic, ToJSON)

instance FromJSON Gist where
  parseJSON =
    withObject "gist" $ \o -> do
      _gistGitPushUrl <- o .: "git_push_url"
      _gistOwner <- o .: "owner"
      _gistFiles <-
        Map.elems <$> ((o .: "files") :: Parser (Map String GistFile))
      _gistTruncated <- o .: "truncated"
      pure Gist {..}

instance FromJSON Owner where
  parseJSON = defaultParseJSON

instance FromJSON GistFile where
  parseJSON = defaultParseJSON

------------------------------------------------------------
k :: IO ()
k = runStdoutLoggingT main

main :: (MonadLogger m, MonadIO m, MonadOAuth m, MonadWeb m) => m ()
main = do
  logInfoT "START"
  result <-
    runExceptT $ do
      config <- loadConfig
      runReaderT fetchTimeline config
  logInfoN $ Text.pack $ show result
  logInfoT "END"
