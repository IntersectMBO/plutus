module BlocklyEditor.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import BlocklyComponent.Types as Blockly

data Action
  = Init
  | HandleBlocklyMessage Blockly.Message
  | InitBlocklyProject String
  | SendToSimulator
  | ViewAsMarlowe
  | Save

defaultEvent :: String -> Event
defaultEvent s = (A.defaultEvent $ "BlocklyEditor." <> s) { category = Just "Blockly" }

instance blocklyActionIsEvent :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent (HandleBlocklyMessage _) = Just $ defaultEvent "HandleBlocklyMessage"
  toEvent (InitBlocklyProject _) = Just $ defaultEvent "InitBlocklyProject"
  toEvent SendToSimulator = Just $ defaultEvent "SendToSimulator"
  toEvent ViewAsMarlowe = Just $ defaultEvent "ViewAsMarlowe"
  toEvent Save = Just $ defaultEvent "Save"

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
