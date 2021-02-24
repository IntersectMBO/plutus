module Template.Lenses
  ( _template
  , _contractNickname
  , _roleWallets
  , _templateContent
  , _name
  , _type
  , _description
  , _extendedContract
  ) where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Symbol (SProxy(..))
import Template.Types (State, Template)
import Marlowe.Extended (Contract, TemplateContent)

_template :: Lens' State Template
_template = prop (SProxy :: SProxy "template")

_contractNickname :: Lens' State String
_contractNickname = prop (SProxy :: SProxy "contractNickname")

_roleWallets :: Lens' State (Map String String)
_roleWallets = prop (SProxy :: SProxy "roleWallets")

_templateContent :: Lens' State TemplateContent
_templateContent = prop (SProxy :: SProxy "templateContent")

------------------------------------------------------------
_name :: Lens' Template String
_name = prop (SProxy :: SProxy "name")

_type :: Lens' Template String
_type = prop (SProxy :: SProxy "type_")

_description :: Lens' Template String
_description = prop (SProxy :: SProxy "description")

_extendedContract :: Lens' Template Contract
_extendedContract = prop (SProxy :: SProxy "extendedContract")
