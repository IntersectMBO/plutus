module Contract.Lenses
  ( _tab
  , _executionState
  , _contractId
  , _confirmation
  , _step
  , _metadata
  , _participants
  , _mActiveUserParty
  ) where

import Contract.Types (State, Tab)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import Marlowe.Execution (ExecutionState)
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Semantics as Semantic
import WalletData.Types (Nickname)

_tab :: Lens' State Tab
_tab = prop (SProxy :: SProxy "tab")

_executionState :: Lens' State ExecutionState
_executionState = prop (SProxy :: SProxy "executionState")

_contractId :: Lens' State (Maybe String)
_contractId = prop (SProxy :: SProxy "contractId")

_confirmation :: Lens' State (Maybe Semantic.Input)
_confirmation = prop (SProxy :: SProxy "confirmation")

_step :: Lens' State Int
_step = prop (SProxy :: SProxy "step")

_metadata :: Lens' State MetaData
_metadata = prop (SProxy :: SProxy "metadata")

_participants :: Lens' State (Map Semantic.Party (Maybe Nickname))
_participants = prop (SProxy :: SProxy "participants")

_mActiveUserParty :: Lens' State (Maybe Semantic.Party)
_mActiveUserParty = prop (SProxy :: SProxy "mActiveUserParty")
