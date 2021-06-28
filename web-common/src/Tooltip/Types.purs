module Tooltip.Types where

import Prelude
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Halogen (RefLabel(..))
import Popper (Placement, PopperInstance)

newtype ReferenceId
  = RefId String

derive instance newtypeReferenceId :: Newtype ReferenceId _

derive newtype instance eqReferenceId :: Eq ReferenceId

derive newtype instance ordReferenceId :: Ord ReferenceId

type State
  = { message :: String
    , active :: Boolean
    , reference :: ReferenceId
    , placement :: Placement
    , mPopperInstance :: Maybe PopperInstance
    }

type Input
  = { message :: String
    , reference :: ReferenceId
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
