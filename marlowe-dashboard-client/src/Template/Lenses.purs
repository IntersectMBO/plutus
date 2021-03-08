module Template.Lenses
  ( _template
  , _contractNickname
  , _roleWallets
  , _templateContent
  , _metaData
  , _extendedContract
  , _contractType
  , _contractDescription
  , _slotParameterDescriptions
  , _valueParameterDescriptions
  , _choiceDescriptions
  ) where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Symbol (SProxy(..))
import Marlowe.Extended (Contract, ContractTemplate, ContractType, MetaData, TemplateContent)
import Marlowe.Semantics (TokenName)
import Template.Types (State)

_template :: Lens' State ContractTemplate
_template = prop (SProxy :: SProxy "template")

_contractNickname :: Lens' State String
_contractNickname = prop (SProxy :: SProxy "contractNickname")

_roleWallets :: Lens' State (Map String String)
_roleWallets = prop (SProxy :: SProxy "roleWallets")

_templateContent :: Lens' State TemplateContent
_templateContent = prop (SProxy :: SProxy "templateContent")

------------------------------------------------------------
_metaData :: Lens' ContractTemplate MetaData
_metaData = prop (SProxy :: SProxy "metaData")

_extendedContract :: Lens' ContractTemplate Contract
_extendedContract = prop (SProxy :: SProxy "extendedContract")

------------------------------------------------------------
_contractType :: Lens' MetaData ContractType
_contractType = prop (SProxy :: SProxy "contractType")

_contractDescription :: Lens' MetaData String
_contractDescription = prop (SProxy :: SProxy "contractDescription")

_roleDescriptions :: Lens' MetaData (Map TokenName String)
_roleDescriptions = prop (SProxy :: SProxy "roleDescriptions")

_slotParameterDescriptions :: Lens' MetaData (Map String String)
_slotParameterDescriptions = prop (SProxy :: SProxy "slotParameterDescriptions")

_valueParameterDescriptions :: Lens' MetaData (Map String String)
_valueParameterDescriptions = prop (SProxy :: SProxy "valueParameterDescriptions")

_choiceDescriptions :: Lens' MetaData (Map String String)
_choiceDescriptions = prop (SProxy :: SProxy "choiceDescriptions")
