module BlocklyEditor.Types where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import BlocklyComponent.Types as Blockly

data Action
  = HandleBlocklyMessage Blockly.Message
  | InitBlocklyProject String
  | SendToSimulator
  | ViewAsMarlowe
  | Save

instance blocklyActionIsEvent :: IsEvent Action where
  toEvent (HandleBlocklyMessage _) = Just $ (defaultEvent "HandleBlocklyMessage") { category = Just "Blockly" }
  toEvent (InitBlocklyProject _) = Just $ (defaultEvent "InitBlocklyProject") { category = Just "Blockly" }
  toEvent SendToSimulator = Just $ (defaultEvent "SendToSimulator") { category = Just "Blockly" }
  toEvent ViewAsMarlowe = Just $ (defaultEvent "ViewAsMarlowe") { category = Just "Blockly" }
  toEvent Save = Just $ (defaultEvent "Save") { category = Just "Blockly" }

type State
  = { errorMessage :: Maybe String
    , marloweCode :: Maybe String
    , hasHoles :: Boolean
    }

_errorMessage :: Lens' State (Maybe String)
_errorMessage = prop (SProxy :: SProxy "errorMessage")

_marloweCode :: Lens' State (Maybe String)
_marloweCode = prop (SProxy :: SProxy "marloweCode")

_hasHoles :: Lens' State Boolean
_hasHoles = prop (SProxy :: SProxy "hasHoles")

initialState :: State
initialState =
  { errorMessage: Nothing
  , marloweCode: Nothing
  , hasHoles: false
  }
