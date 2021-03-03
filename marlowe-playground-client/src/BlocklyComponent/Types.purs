module BlocklyComponent.Types where

import Prelude hiding (div)
import Blockly.Dom (Block)
import Blockly.Internal (BlockDefinition, XML)
import Blockly.Types as BT
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.List (List)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Halogen (RefLabel(..), SubscriptionId)
import Marlowe.Linter (Warning)

type State
  = { blocklyState :: Maybe BT.BlocklyState
    , errorMessage :: Maybe String
    , blocklyEventSubscription :: Maybe SubscriptionId
    , eventsWhileDragging :: Maybe (List BT.BlocklyEvent)
    }

_blocklyState :: Lens' State (Maybe BT.BlocklyState)
_blocklyState = prop (SProxy :: SProxy "blocklyState")

_errorMessage :: Lens' State (Maybe String)
_errorMessage = prop (SProxy :: SProxy "errorMessage")

_blocklyEventSubscription :: Lens' State (Maybe SubscriptionId)
_blocklyEventSubscription = prop (SProxy :: SProxy "blocklyEventSubscription")

emptyState :: State
emptyState =
  { blocklyState: Nothing
  , errorMessage: Nothing
  , blocklyEventSubscription: Nothing
  , eventsWhileDragging: Nothing
  }

data Query a
  = SetCode String a
  | SetError String a
  | GetWorkspace (XML -> a)
  | LoadWorkspace XML a
  | GetBlockRepresentation (Block -> a)
  | SelectWarning Warning a

data Action
  = Inject String (Array BlockDefinition)
  | SetData Unit
  | BlocklyEvent BT.BlocklyEvent
  | ResizeWorkspace
  | VisibilityChanged Boolean

data Message
  = CodeChange

blocklyRef :: RefLabel
blocklyRef = RefLabel "blockly"
