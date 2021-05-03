module Capability.Websocket
  ( class MonadWebsocket
  , subscribeToWallet
  , unsubscribeFromWallet
  , subscribeToPlutusApp
  , unsubscribeFromPlutusApp
  ) where

import Prelude
import AppM (AppM)
import Bridge (toBack)
import Data.Either (Either(..))
import Halogen (HalogenM, raise)
import MainFrame.Types (Msg(..))
import Marlowe.PAB (PlutusAppId)
import Plutus.PAB.Webserver.Types (CombinedWSStreamToServer(..))
import WalletData.Types (Wallet)

class
  Monad m <= MonadWebsocket m where
  subscribeToWallet :: Wallet -> m Unit
  unsubscribeFromWallet :: Wallet -> m Unit
  subscribeToPlutusApp :: PlutusAppId -> m Unit
  unsubscribeFromPlutusApp :: PlutusAppId -> m Unit

-- we can only send websocket messages in a HalogenM monad, but the compiler requires an AppM instance as well
instance monadWebsocketAppM :: MonadWebsocket AppM where
  subscribeToWallet wallet = pure unit
  unsubscribeFromWallet wallet = pure unit
  subscribeToPlutusApp plutusAppId = pure unit
  unsubscribeFromPlutusApp plutusAppId = pure unit

instance monadWebsocketHalogenM :: MonadWebsocket (HalogenM state action slots Msg m) where
  subscribeToWallet wallet = raise $ SendWebSocketMessage $ Subscribe $ Right $ toBack wallet
  unsubscribeFromWallet wallet = raise $ SendWebSocketMessage $ Unsubscribe $ Right $ toBack wallet
  subscribeToPlutusApp plutusAppId = raise $ SendWebSocketMessage $ Subscribe $ Left $ toBack plutusAppId
  unsubscribeFromPlutusApp plutusAppId = raise $ SendWebSocketMessage $ Unsubscribe $ Left $ toBack plutusAppId
