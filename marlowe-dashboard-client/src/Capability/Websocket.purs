module Capability.Websocket
  ( class MonadWebsocket
  , subscribeToWallet
  , unsubscribeFromWallet
  , subscribeToContract
  , unsubscribeFromContract
  ) where

import Prelude
import AppM (AppM)
import Bridge (toBack)
import Data.Either (Either(..))
import Halogen (HalogenM, raise)
import MainFrame.Types (Msg(..))
import Marlowe.PAB (ContractInstanceId)
import Plutus.PAB.Webserver.Types (CombinedWSStreamToServer(..))
import WalletData.Types (Wallet)

class
  Monad m <= MonadWebsocket m where
  subscribeToWallet :: Wallet -> m Unit
  unsubscribeFromWallet :: Wallet -> m Unit
  subscribeToContract :: ContractInstanceId -> m Unit
  unsubscribeFromContract :: ContractInstanceId -> m Unit

-- we can only send websocket messages in a HalogenM monad, but the compiler requires an AppM instance as well
instance monadWebsocketAppM :: MonadWebsocket AppM where
  subscribeToWallet wallet = pure unit
  unsubscribeFromWallet wallet = pure unit
  subscribeToContract contractInstanceId = pure unit
  unsubscribeFromContract contractInstanceId = pure unit

instance monadWebsocketHalogenM :: MonadWebsocket (HalogenM state action slots Msg m) where
  subscribeToWallet wallet = raise $ SendWebSocketMessage $ Subscribe $ Right $ toBack wallet
  unsubscribeFromWallet wallet = raise $ SendWebSocketMessage $ Unsubscribe $ Right $ toBack wallet
  subscribeToContract contractInstanceId = pure unit --raise $ SendWebSocketMessage $ Subscribe $ Left $ toBack contractInstanceId
  unsubscribeFromContract contractInstanceId = pure unit --raise $ SendWebSocketMessage $ Unsubscribe $ Left $ toBack contractInstanceId
