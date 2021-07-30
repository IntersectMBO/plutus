module Template.Lenses
  ( _contractSetupStage
  , _contractTemplate
  , _contractNicknameInput
  , _roleWalletInputs
  , _roleWalletInput
  , _slotContentInputs
  , _slotContentInput
  , _valueContentInputs
  , _valueContentInput
  ) where

import Prelude
import Data.Lens (Lens', Traversal')
import Data.Lens.At (at)
import Data.Lens.Prism.Maybe (_Just)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Symbol (SProxy(..))
import InputField.Types (State) as InputField
import Marlowe.Extended.Metadata (ContractTemplate)
import Marlowe.Semantics (TokenName)
import Template.Types (ContractSetupStage, ContractNicknameError, RoleError, SlotError, State, ValueError)

_contractSetupStage :: Lens' State ContractSetupStage
_contractSetupStage = prop (SProxy :: SProxy "contractSetupStage")

_contractTemplate :: Lens' State ContractTemplate
_contractTemplate = prop (SProxy :: SProxy "contractTemplate")

_contractNicknameInput :: Lens' State (InputField.State ContractNicknameError)
_contractNicknameInput = prop (SProxy :: SProxy "contractNicknameInput")

_roleWalletInputs :: Lens' State (Map TokenName (InputField.State RoleError))
_roleWalletInputs = prop (SProxy :: SProxy "roleWalletInputs")

_roleWalletInput :: TokenName -> Traversal' State (InputField.State RoleError)
_roleWalletInput tokenName = _roleWalletInputs <<< at tokenName <<< _Just

_slotContentInputs :: Lens' State (Map String (InputField.State SlotError))
_slotContentInputs = prop (SProxy :: SProxy "slotContentInputs")

_slotContentInput :: String -> Traversal' State (InputField.State SlotError)
_slotContentInput key = _slotContentInputs <<< at key <<< _Just

_valueContentInputs :: Lens' State (Map String (InputField.State ValueError))
_valueContentInputs = prop (SProxy :: SProxy "valueContentInputs")

_valueContentInput :: String -> Traversal' State (InputField.State ValueError)
_valueContentInput key = _valueContentInputs <<< at key <<< _Just
