module Capability.Ajax (runAjax) where

import Prelude
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (class MonadAsk, ReaderT)
import Control.Monad.Reader.Extra (mapEnvReaderT)
import Env (Env)
import Network.RemoteData (fromEither)
import Plutus.PAB.Webserver (SPParams_)
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import Types (WebData)

runAjax :: forall a m. MonadAsk Env m => ExceptT AjaxError (ReaderT (SPSettings_ SPParams_) m) a -> m (WebData a)
runAjax action = mapEnvReaderT _.ajaxSettings $ fromEither <$> runExceptT action
