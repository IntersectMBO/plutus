module Contract.Lenses
  ( _tab
  , _executionState
  , _previousSteps
  , _marloweParams
  , _contractInstanceId
  , _selectedStep
  , _metadata
  , _participants
  , _namedActions
  ) where

import Contract.Types (PreviousStep, State, Tab)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import Marlowe.Execution (ExecutionState, NamedAction)
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.PAB (ContractInstanceId, MarloweParams)
import Marlowe.Semantics as Semantic
import WalletData.Types (WalletNickname)

_tab :: Lens' State Tab
_tab = prop (SProxy :: SProxy "tab")

_executionState :: Lens' State ExecutionState
_executionState = prop (SProxy :: SProxy "executionState")

_previousSteps :: Lens' State (Array PreviousStep)
_previousSteps = prop (SProxy :: SProxy "previousSteps")

_marloweParams :: Lens' State MarloweParams
_marloweParams = prop (SProxy :: SProxy "marloweParams")

_contractInstanceId :: Lens' State ContractInstanceId
_contractInstanceId = prop (SProxy :: SProxy "contractInstanceId")

_selectedStep :: Lens' State Int
_selectedStep = prop (SProxy :: SProxy "selectedStep")

_metadata :: Lens' State MetaData
_metadata = prop (SProxy :: SProxy "metadata")

_participants :: Lens' State (Map Semantic.Party (Maybe WalletNickname))
_participants = prop (SProxy :: SProxy "participants")

_namedActions :: Lens' State (Array NamedAction)
_namedActions = prop (SProxy :: SProxy "namedActions")
