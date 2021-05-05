module Capability.Websocket
  ( class ManageWebsocket
  , subscribeToWallet
  , unsubscribeFromWallet
  , subscribeToContract
  , unsubscribeFromContract
  ) where

import Prelude
import AppM (AppM)
import Data.Either (Either(..))
import Halogen (HalogenM, raise)
import MainFrame.Types (Msg(..))
import Plutus.PAB.Webserver.Types (CombinedWSStreamToServer(..))
import Wallet.Emulator.Wallet (Wallet)
import Wallet.Types (ContractInstanceId)

class
  Monad m <= ManageWebsocket m where
  subscribeToWallet :: Wallet -> m Unit
  unsubscribeFromWallet :: Wallet -> m Unit
  subscribeToContract :: ContractInstanceId -> m Unit
  unsubscribeFromContract :: ContractInstanceId -> m Unit

-- we can only send websocket messages in a HalogenM monad, but the compiler requires an AppM instance as well
instance manageWebsocketAppM :: ManageWebsocket AppM where
  subscribeToWallet wallet = pure unit
  unsubscribeFromWallet wallet = pure unit
  subscribeToContract contractInstanceId = pure unit
  unsubscribeFromContract contractInstanceId = pure unit

instance manageWebsocketHalogenM :: ManageWebsocket (HalogenM state action slots Msg m) where
  subscribeToWallet wallet = raise $ SendWebSocketMessage $ Subscribe $ Right wallet
  unsubscribeFromWallet wallet = raise $ SendWebSocketMessage $ Unsubscribe $ Right wallet
  subscribeToContract contractInstanceId = raise $ SendWebSocketMessage $ Subscribe $ Left contractInstanceId
  unsubscribeFromContract contractInstanceId = raise $ SendWebSocketMessage $ Unsubscribe $ Left contractInstanceId
