module Contract.Lenses
  ( _tab
  , _executionState
  , _contractId
  , _side
  , _confirmation
  , _step
  ) where

import Contract.Types (Side, State, Tab)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import Marlowe.Execution (ExecutionState)
import Marlowe.Semantics (Input)

_tab :: Lens' State Tab
_tab = prop (SProxy :: SProxy "tab")

_executionState :: Lens' State ExecutionState
_executionState = prop (SProxy :: SProxy "executionState")

_contractId :: Lens' State (Maybe String)
_contractId = prop (SProxy :: SProxy "contractId")

_side :: Lens' State Side
_side = prop (SProxy :: SProxy "side")

_confirmation :: Lens' State (Maybe Input)
_confirmation = prop (SProxy :: SProxy "confirmation")

_step :: Lens' State Int
_step = prop (SProxy :: SProxy "step")
