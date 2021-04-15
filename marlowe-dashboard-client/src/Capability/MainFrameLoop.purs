module Capability.MainFrameLoop where

import Prelude
import AppM (AppM)
import Halogen (HalogenM, raise)
import MainFrame.Types (Msg(..), Action)

-- This capability allows child components to trigger an action in the MainFrame. It uses
-- a loop between a MainFrame output message and a MainFrame query, which was the only way
-- I was able to call a parent handleAction from a child.
class
  Monad m <= MainFrameLoop m where
  callMainFrameAction :: Action -> m Unit

-- There is nothing pertinent to do inside the AppM, but we need to provide this instance to
-- satisfy the compiler
instance mainFrameLoopAppM :: MainFrameLoop AppM where
  callMainFrameAction toast = pure unit

instance mainFrameLoopHalogenM :: MainFrameLoop (HalogenM state action slots Msg m) where
  callMainFrameAction action = raise $ MainFrameActionMsg action
