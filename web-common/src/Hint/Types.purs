module Hint.Types where

import Data.Maybe (Maybe)
import Halogen (RefLabel(..), SubscriptionId)
import Halogen.HTML (PlainHTML)
import Popper (Placement, PopperInstance)

type State
  = { content :: PlainHTML
    , active :: Boolean
    , placement :: Placement
    -- The placement of the hint icon (the "?" icon) is a responsability of
    -- the parent (whoever includes the hint).
    , hintElementClasses :: Array String
    , mPopperInstance :: Maybe PopperInstance
    -- When the hint is active we keep track of clicks in the window to close
    -- the hint if the click was made outside of the dialog. We need to keep
    -- the subscription in the state to clear it once the hint closes.
    , mGlobalClickSubscription :: Maybe SubscriptionId
    }

type Input
  = { hintElementClasses :: Array String
    , content :: PlainHTML
    , placement :: Placement
    }

data Action
  = Init
  | Finalize
  | OnNewInput Input
  | Open
  | Close
  | Toggle

hintRef :: RefLabel
hintRef = (RefLabel "hint")

popoutRef :: RefLabel
popoutRef = (RefLabel "popout")

arrowRef :: RefLabel
arrowRef = (RefLabel "arrow")
