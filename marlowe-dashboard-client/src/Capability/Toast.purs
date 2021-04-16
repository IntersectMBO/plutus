module Capability.Toast where

import Prelude
import AppM (AppM)
import Capability.MainFrameLoop (class MainFrameLoop, callMainFrameAction)
import Halogen (HalogenM)
import MainFrame.Types (Action(..), Msg) as MainFrame
import Toast.Types (ToastMessage, Action(..))

-- This class allows any component to trigger a toast notification
class
  MainFrameLoop m <= Toast m where
  addToast :: ToastMessage -> m Unit

-- There is nothing pertinent to do inside the AppM, but we need to provide this instance to
-- satisfy the compiler
instance toastAppM :: Toast AppM where
  addToast toast = pure unit

instance toastHalogenM :: Toast (HalogenM state action slots MainFrame.Msg m) where
  addToast toast = callMainFrameAction $ MainFrame.ToastAction $ AddToast toast
