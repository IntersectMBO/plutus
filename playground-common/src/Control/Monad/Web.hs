module Control.Monad.Web
  ( MonadWeb
  , doRequest
  , makeManager
  ) where

import           Auth.Types                (addUserAgent)
import           Control.Monad.Except      (ExceptT)
import           Control.Monad.Logger      (LoggingT)
import           Control.Monad.Reader      (ReaderT)
import           Control.Monad.Trans.Class (lift)
import qualified Data.ByteString.Lazy      as LBS
import           Data.Text                 (Text)
import           Network.HTTP.Client       (managerModifyRequest)
import           Network.HTTP.Client.TLS   (tlsManagerSettings)
import           Network.HTTP.Conduit      (Manager, Request, Response, httpLbs, newManager)

class Monad m =>
      MonadWeb m
  where
  makeManager :: m Manager
  doRequest :: Manager -> Request -> m (Either Text (Response LBS.ByteString))

instance MonadWeb IO where
  makeManager = newManager $ tlsManagerSettings {managerModifyRequest = pure . addUserAgent}
  doRequest manager request = Right <$> httpLbs request manager

instance MonadWeb m => MonadWeb (LoggingT m) where
  makeManager = lift makeManager
  doRequest manager = lift . doRequest manager


instance MonadWeb m => MonadWeb (ExceptT e m) where
  makeManager = lift makeManager
  doRequest manager = lift . doRequest manager

instance MonadWeb m => MonadWeb (ReaderT a m) where
  makeManager = lift makeManager
  doRequest manager = lift . doRequest manager
