module Contract.Lenses
  ( _Starting
  , _Started
  , _nickname
  , _tab
  , _executionState
  , _pendingTransaction
  , _previousSteps
  , _marloweParams
  , _selectedStep
  , _metadata
  , _participants
  , _userParties
  , _namedActions
  , _expandPayments
  , _resultingPayments
  , _stateNickname
  , _stateMetadata
  , _stateParticipants
  ) where

import Prologue
import Contract.Types (StartedState, State(..), StartingState)
import Data.Lens (Lens', Prism', lens', prism')
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Symbol (SProxy(..))
import Data.Tuple.Nested ((/\))
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Semantics (Party)
import Contacts.Types (WalletNickname)

_Starting :: Prism' State StartingState
_Starting =
  prism'
    Starting
    ( case _ of
        Starting s -> Just s
        _ -> Nothing
    )

_Started :: Prism' State StartedState
_Started =
  prism'
    Started
    ( case _ of
        Started s -> Just s
        _ -> Nothing
    )

_nickname :: forall a r. Lens' { nickname :: a | r } a
_nickname = prop (SProxy :: SProxy "nickname")

_stateNickname :: Lens' State String
_stateNickname = lens' go
  where
  go (Starting s) = s.nickname /\ Starting <<< s { nickname = _ }

  go (Started s) = s.nickname /\ Started <<< s { nickname = _ }

_tab :: forall a r. Lens' { tab :: a | r } a
_tab = prop (SProxy :: SProxy "tab")

_executionState :: forall a r. Lens' { executionState :: a | r } a
_executionState = prop (SProxy :: SProxy "executionState")

_pendingTransaction :: forall a r. Lens' { pendingTransaction :: a | r } a
_pendingTransaction = prop (SProxy :: SProxy "pendingTransaction")

_previousSteps :: forall a r. Lens' { previousSteps :: a | r } a
_previousSteps = prop (SProxy :: SProxy "previousSteps")

_marloweParams :: forall a r. Lens' { marloweParams :: a | r } a
_marloweParams = prop (SProxy :: SProxy "marloweParams")

_selectedStep :: forall a r. Lens' { selectedStep :: a | r } a
_selectedStep = prop (SProxy :: SProxy "selectedStep")

_metadata :: forall a r. Lens' { metadata :: a | r } a
_metadata = prop (SProxy :: SProxy "metadata")

_stateMetadata :: Lens' State MetaData
_stateMetadata = lens' go
  where
  go (Starting s) = s.metadata /\ Starting <<< s { metadata = _ }

  go (Started s) = s.metadata /\ Started <<< s { metadata = _ }

_participants :: forall a r. Lens' { participants :: a | r } a
_participants = prop (SProxy :: SProxy "participants")

_stateParticipants :: Lens' State (Map Party (Maybe WalletNickname))
_stateParticipants = lens' go
  where
  go (Starting s) = s.participants /\ Starting <<< s { participants = _ }

  go (Started s) = s.participants /\ Started <<< s { participants = _ }

_userParties :: forall a r. Lens' { userParties :: a | r } a
_userParties = prop (SProxy :: SProxy "userParties")

_namedActions :: forall a r. Lens' { namedActions :: a | r } a
_namedActions = prop (SProxy :: SProxy "namedActions")

_expandPayments :: forall a r. Lens' { expandPayments :: a | r } a
_expandPayments = prop (SProxy :: SProxy "expandPayments")

_resultingPayments :: forall a r. Lens' { resultingPayments :: a | r } a
_resultingPayments = prop (SProxy :: SProxy "resultingPayments")
