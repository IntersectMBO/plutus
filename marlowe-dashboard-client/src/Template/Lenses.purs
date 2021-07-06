module Template.Lenses
  ( _template
  , _contractNickname
  , _roleWalletInputs
  , _roleWalletInput
  , _templateContent
  , _slotContentStrings
  , _dummyNumberInput
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
import Marlowe.Template (TemplateContent)
import Template.Types (State)
import Template.Validation (RoleError)

_template :: Lens' State ContractTemplate
_template = prop (SProxy :: SProxy "template")

_contractNickname :: Lens' State String
_contractNickname = prop (SProxy :: SProxy "contractNickname")

_roleWalletInputs :: Lens' State (Map TokenName (InputField.State RoleError))
_roleWalletInputs = prop (SProxy :: SProxy "roleWalletInputs")

_roleWalletInput :: TokenName -> Traversal' State (InputField.State RoleError)
_roleWalletInput tokenName = _roleWalletInputs <<< at tokenName <<< _Just

_templateContent :: Lens' State TemplateContent
_templateContent = prop (SProxy :: SProxy "templateContent")

_slotContentStrings :: Lens' State (Map String String)
_slotContentStrings = prop (SProxy :: SProxy "slotContentStrings")

_dummyNumberInput :: Lens' State (InputField.State RoleError)
_dummyNumberInput = prop (SProxy :: SProxy "dummyNumberInput")
