module Tooltip.Types where

import Prelude
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Halogen (RefLabel(..))
import Popper (Placement, PopperInstance)

newtype RefferenceId
  = RefId String

derive instance newtypeRefferenceId :: Newtype RefferenceId _

derive newtype instance eqRefferenceId :: Eq RefferenceId

derive newtype instance ordRefferenceId :: Ord RefferenceId

type State
  = { message :: String
    , active :: Boolean
    , reference :: RefferenceId
    , placement :: Placement
    , mPopperInstance :: Maybe PopperInstance
    }

type Input
  = { message :: String
    , reference :: RefferenceId
    , placement :: Placement
    }

data Action
  = Init
  | Finalize
  | OnNewInput Input
  | Show
  | Hide

tooltipRef :: RefLabel
tooltipRef = (RefLabel "tooltip")

arrowRef :: RefLabel
arrowRef = (RefLabel "arrow")
