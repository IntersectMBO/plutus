module Template.Lenses
  ( _template
  , _contractNickname
  , _roleWalletInputs
  , _roleWalletInput
  , _templateContent
  , _slotContentStrings
  , _metaData
  , _extendedContract
  , _contractType
  , _contractName
  , _slotParameterDescriptions
  , _valueParameterDescriptions
  ) where

import Prelude
import Data.Lens (Lens', Traversal')
import Data.Lens.At (at)
import Data.Lens.Prism.Maybe (_Just)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Symbol (SProxy(..))
import InputField.Types (State) as InputField
import Marlowe.Extended (Contract, ContractType)
import Marlowe.Extended.Metadata (ContractTemplate, MetaData, ChoiceInfo)
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

------------------------------------------------------------
_metaData :: Lens' ContractTemplate MetaData
_metaData = prop (SProxy :: SProxy "metaData")

_extendedContract :: Lens' ContractTemplate Contract
_extendedContract = prop (SProxy :: SProxy "extendedContract")

------------------------------------------------------------
_contractType :: Lens' MetaData ContractType
_contractType = prop (SProxy :: SProxy "contractType")

_contractName :: Lens' MetaData String
_contractName = prop (SProxy :: SProxy "contractName")

_contractDescription :: Lens' MetaData String
_contractDescription = prop (SProxy :: SProxy "contractDescription")

_roleDescriptions :: Lens' MetaData (Map TokenName String)
_roleDescriptions = prop (SProxy :: SProxy "roleDescriptions")

_slotParameterDescriptions :: Lens' MetaData (Map String String)
_slotParameterDescriptions = prop (SProxy :: SProxy "slotParameterDescriptions")

_valueParameterDescriptions :: Lens' MetaData (Map String String)
_valueParameterDescriptions = prop (SProxy :: SProxy "valueParameterDescriptions")
