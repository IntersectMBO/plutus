{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Utils
  ( withError
  , makeManager
  , defaultParseJSON
  , defaultToJSON
  , addUserAgent
  , logDebugT
  , logErrorT
  , logInfoT
  , logException
  , MonadOAuth
  , sign
  , MonadWeb
  , doRequest
  , OAuthCode(OAuthCode)
  , OAuthToken(..)
  , TokenProvider(..)
  , Token(..)
  ) where

import           Control.Monad.Except        (ExceptT, MonadError, runExceptT, throwError)
import           Control.Monad.Logger        (LoggingT, MonadLogger, logDebugN, logErrorN, logInfoN)
import           Control.Monad.Reader        (ReaderT)
import           Control.Monad.Trans.Class   (lift)
import           Control.Newtype.Generics    (Newtype)
import           Data.Aeson                  (FromJSON, GFromJSON, GToJSON, ToJSON, Value, Zero, genericParseJSON,
                                              genericToJSON, parseJSON)
import           Data.Aeson.Casing           (aesonDrop, aesonPrefix, snakeCase)
import           Data.Aeson.Types            (Parser)
import qualified Data.ByteString.Lazy        as LBS
import           Data.Text                   (Text)
import qualified Data.Text                   as T
import           GHC.Generics                (Generic, Rep)
import           Network.HTTP.Client.Conduit (defaultManagerSettings)
import           Network.HTTP.Conduit        (Manager, Request, Response, httpLbs, newManager)
import           Network.HTTP.Simple         (addRequestHeader)
import           Network.HTTP.Types          (hUserAgent)
import           Servant                     (FromHttpApiData, ToHttpApiData, parseQueryParam, toUrlPiece)
import           Web.Authenticate.OAuth      (Credential, OAuth, signOAuth)

------------------------------------------------------------
class Monad m =>
      MonadOAuth m
  where
  sign :: OAuth -> Credential -> Request -> m Request

instance MonadOAuth IO where
  sign = signOAuth

instance MonadOAuth m => MonadOAuth (LoggingT m) where
  sign oauth credential = lift . sign oauth credential

instance MonadOAuth m => MonadOAuth (ReaderT a m) where
  sign oauth credential = lift . sign oauth credential

instance MonadOAuth m => MonadOAuth (ExceptT e m) where
  sign oauth credential = lift . sign oauth credential

------------------------------------------------------------
class Monad m =>
      MonadWeb m
  where
  makeManager :: m Manager
  doRequest :: Request -> Manager -> m (Either Text (Response LBS.ByteString))

instance MonadWeb IO where
  makeManager = newManager defaultManagerSettings
  doRequest request manager = Right <$> httpLbs request manager

instance MonadWeb m => MonadWeb (LoggingT m) where
  makeManager = lift makeManager
  doRequest request = lift . doRequest request

instance MonadWeb m => MonadWeb (ExceptT e m) where
  makeManager = lift makeManager
  doRequest request = lift . doRequest request

instance MonadWeb m => MonadWeb (ReaderT a m) where
  makeManager = lift makeManager
  doRequest request = lift . doRequest request

------------------------------------------------------------
logDebugT :: MonadLogger m => String -> m ()
logDebugT = logDebugN . T.pack

logInfoT :: MonadLogger m => String -> m ()
logInfoT = logInfoN . T.pack

logErrorT :: MonadLogger m => String -> m ()
logErrorT = logErrorN . T.pack

------------------------------------------------------------
runException :: Monad m => (e -> m b) -> (a -> m b) -> ExceptT e m a -> m b
runException bad good f = do
  result <- runExceptT f
  either bad good result

logException :: (Show e, MonadLogger m) => ExceptT e m () -> m ()
logException = runException (logErrorT . show) return

withError :: MonadError e' m => (e -> e') -> Either e a -> m a
withError wrapper = either (throwError . wrapper) pure

defaultParseJSON :: (Generic a, GFromJSON Zero (Rep a)) => Value -> Parser a
defaultParseJSON = genericParseJSON $ aesonPrefix snakeCase

defaultToJSON :: (Generic a, GToJSON Zero (Rep a)) => a -> Value
defaultToJSON = genericToJSON $ aesonPrefix snakeCase

newtype OAuthCode =
  OAuthCode Text
  deriving (Show, Eq)

instance FromHttpApiData OAuthCode where
  parseQueryParam = Right . OAuthCode

data OAuthToken a = OAuthToken
  { oAuthTokenAccessToken :: Token a
  , oAuthTokenScope       :: Text
  , oAuthTokenTokenType   :: Text
  } deriving (Show, Eq, Generic)

-- | We use the default JSON encoding for sending-to-PureScript's
-- sake, but a custom one for receiving-from-Github.
instance ToJSON (OAuthToken a)

instance FromJSON (OAuthToken a) where
  parseJSON = genericParseJSON $ aesonDrop 10 snakeCase

------------------------------------------------------------
data TokenProvider =
  Github

newtype Token (a :: TokenProvider) =
  Token Text
  deriving stock (Show, Eq,Generic)
  deriving newtype (FromJSON,ToJSON)
  deriving anyclass (Newtype)

instance ToHttpApiData (Token a) where
  toUrlPiece (Token token) = "token " <> token

addUserAgent :: Request -> Request
addUserAgent = addRequestHeader hUserAgent "haskell-conduit"
