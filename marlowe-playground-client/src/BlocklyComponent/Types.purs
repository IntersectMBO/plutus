module BlocklyComponent.Types where

import Prelude hiding (div)
import Blockly.Internal (BlockDefinition, XML)
import Blockly.Generator (Generator)
import Blockly.Types as BT
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))

type State
  = { blocklyState :: Maybe BT.BlocklyState
    , generator :: Maybe Generator
    , errorMessage :: Maybe String
    , useEvents :: Boolean
    }

_blocklyState :: Lens' State (Maybe BT.BlocklyState)
_blocklyState = prop (SProxy :: SProxy "blocklyState")

_generator :: Lens' State (Maybe Generator)
_generator = prop (SProxy :: SProxy "generator")

_errorMessage :: Lens' State (Maybe String)
_errorMessage = prop (SProxy :: SProxy "errorMessage")

_useEvents :: Lens' State Boolean
_useEvents = prop (SProxy :: SProxy "useEvents")

emptyState :: State
emptyState = { blocklyState: Nothing, generator: Nothing, errorMessage: Nothing, useEvents: false }

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
