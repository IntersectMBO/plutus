module Contract.Lenses
  ( _nickname
  , _tab
  , _executionState
  , _pendingTransaction
  , _previousSteps
  , _mMarloweParams
  , _followerAppId
  , _selectedStep
  , _metadata
  , _participants
  , _userParties
  , _namedActions
  ) where

import Contract.Types (PreviousStep, State, Tab)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.Set (Set)
import Data.Symbol (SProxy(..))
import Marlowe.Execution.Types (NamedAction)
import Marlowe.Execution.Types (State) as Execution
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.PAB (PlutusAppId, MarloweParams)
import Marlowe.Semantics (Party, TransactionInput)
import WalletData.Types (WalletNickname)

_nickname :: Lens' State String
_nickname = prop (SProxy :: SProxy "nickname")

_tab :: forall a. Lens' { tab :: Tab | a } Tab
_tab = prop (SProxy :: SProxy "tab")

_executionState :: Lens' State Execution.State
_executionState = prop (SProxy :: SProxy "executionState")

_pendingTransaction :: Lens' State (Maybe TransactionInput)
_pendingTransaction = prop (SProxy :: SProxy "pendingTransaction")

_previousSteps :: Lens' State (Array PreviousStep)
_previousSteps = prop (SProxy :: SProxy "previousSteps")

_mMarloweParams :: Lens' State (Maybe MarloweParams)
_mMarloweParams = prop (SProxy :: SProxy "mMarloweParams")

_followerAppId :: Lens' State PlutusAppId
_followerAppId = prop (SProxy :: SProxy "followerAppId")

_selectedStep :: Lens' State Int
_selectedStep = prop (SProxy :: SProxy "selectedStep")

_metadata :: Lens' State MetaData
_metadata = prop (SProxy :: SProxy "metadata")

_participants :: Lens' State (Map Party (Maybe WalletNickname))
_participants = prop (SProxy :: SProxy "participants")

_userParties :: Lens' State (Set Party)
_userParties = prop (SProxy :: SProxy "userParties")

_namedActions :: Lens' State (Array NamedAction)
_namedActions = prop (SProxy :: SProxy "namedActions")
