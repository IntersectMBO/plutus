module BlocklyComponent.Types where

import Prelude hiding (div)
import Blockly.Generator (Generator)
import Blockly.Internal (BlockDefinition, XML)
import Blockly.Types as BT
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.List (List)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Halogen (SubscriptionId)

type State
  = { blocklyState :: Maybe BT.BlocklyState
    -- FIXME: remove
    , generator :: Maybe Generator
    , errorMessage :: Maybe String
    , blocklyEventSubscription :: Maybe SubscriptionId
    , eventsWhileDragging :: Maybe (List BT.BlocklyEvent)
    }

_blocklyState :: Lens' State (Maybe BT.BlocklyState)
_blocklyState = prop (SProxy :: SProxy "blocklyState")

-- FIXME: remove
_generator :: Lens' State (Maybe Generator)
_generator = prop (SProxy :: SProxy "generator")

_errorMessage :: Lens' State (Maybe String)
_errorMessage = prop (SProxy :: SProxy "errorMessage")

_blocklyEventSubscription :: Lens' State (Maybe SubscriptionId)
_blocklyEventSubscription = prop (SProxy :: SProxy "blocklyEventSubscription")

emptyState :: State
emptyState =
  { blocklyState: Nothing
  , generator: Nothing
  , errorMessage: Nothing
  , blocklyEventSubscription: Nothing
  , eventsWhileDragging: Nothing
  }

data Query a
  = Resize a
  | SetCode String a
  | SetError String a
  | GetWorkspace (XML -> a)
  | LoadWorkspace XML a
  | GetCode (String -> a)

data Action
  = Inject String (Array BlockDefinition)
  | SetData Unit
  | BlocklyEvent BT.BlocklyEvent

data Message
  = CodeChange
