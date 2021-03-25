module Capability
  ( class MonadWallet
  , createWallet
  , class MonadContract
  , invokeEndpoint
  ) where

import Prelude
import AppM (AppM)
import Control.Monad.Except (ExceptT, lift, runExceptT)
import Control.Monad.Reader (class MonadAsk, ReaderT)
import Control.Monad.Reader.Extra (mapEnvReaderT)
import Data.Json.JsonUUID (JsonUUID, _JsonUUID)
import Data.Lens (Getter', Lens', to, view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.RawJson (RawJson)
import Data.Symbol (SProxy(..))
import Data.UUID (toString) as UUID
import Env (Env)
import Halogen (HalogenM)
import Network.RemoteData (RemoteData)
import Network.RemoteData (fromEither) as RemoteData
import Plutus.PAB.Webserver (SPParams_, postApiContractByContractinstanceidEndpointByEndpointname, postWalletCreate)
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import Wallet.Emulator.Wallet (Wallet)
import Wallet.Types (ContractInstanceId, EndpointDescription, NotificationError)

class
  Monad m <= MonadWallet m where
  createWallet :: m (RemoteData AjaxError Wallet)

instance monadWalletAppM :: MonadWallet AppM where
  createWallet = runAjax postWalletCreate

instance monadWalletHalogenM :: MonadWallet m => MonadWallet (HalogenM state action slots msg m) where
  createWallet = lift createWallet

class
  Monad m <= MonadContract m where
  invokeEndpoint :: RawJson -> ContractInstanceId -> EndpointDescription -> m (RemoteData AjaxError (Maybe NotificationError))

instance monadContractAppM :: MonadContract AppM where
  invokeEndpoint payload contractInstanceId endpointDescription =
    runAjax
      $ postApiContractByContractinstanceidEndpointByEndpointname
          payload
          (view _contractInstanceIdString contractInstanceId)
          (view _getEndpointDescription endpointDescription)

instance monadContractHalogenM :: MonadContract m => MonadContract (HalogenM state action slots msg m) where
  invokeEndpoint payload contractInstanceId endpointDescription = lift $ invokeEndpoint payload contractInstanceId endpointDescription

runAjax :: forall a m. MonadAsk Env m => ExceptT AjaxError (ReaderT (SPSettings_ SPParams_) m) a -> m (RemoteData AjaxError a)
runAjax action = mapEnvReaderT _.ajaxSettings $ RemoteData.fromEither <$> runExceptT action

_contractInstanceIdString :: Getter' ContractInstanceId String
_contractInstanceIdString = _contractInstanceId <<< _JsonUUID <<< to UUID.toString

_contractInstanceId :: Lens' ContractInstanceId JsonUUID
_contractInstanceId = _Newtype <<< prop (SProxy :: SProxy "unContractInstanceId")

_getEndpointDescription :: forall s r a. Newtype s { getEndpointDescription :: a | r } => Lens' s a
_getEndpointDescription = _Newtype <<< prop (SProxy :: SProxy "getEndpointDescription")
