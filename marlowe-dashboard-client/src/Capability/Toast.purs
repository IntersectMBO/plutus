module Capability.Toast where

import Prelude
import AppM (AppM)
import Halogen (HalogenM, raise)
import MainFrame.Types (Msg(..))
import Toast.Types (Toast)

-- FIXME: Add comments
class
  Monad m <= Toast m where
  addToast :: Toast -> m Unit

instance monadWebsocketAppM :: Toast AppM where
  addToast toast = pure unit

instance toastHalogenM :: Toast (HalogenM state action slots Msg m) where
  addToast toast = raise $ AddToastMsg toast
