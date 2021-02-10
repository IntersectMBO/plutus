module Contact.Lenses
  ( _contacts
  , _newContactKey
  , _userHasPickedUp
  ) where

import Prelude
import Contact.Types (Contact, ContactKey, State)
import Data.Lens (Lens')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Symbol (SProxy(..))

_contacts :: Lens' State (Map ContactKey Contact)
_contacts = prop (SProxy :: SProxy "contacts")

_newContactKey :: Lens' State ContactKey
_newContactKey = prop (SProxy :: SProxy "newContactKey")

_userHasPickedUp :: Lens' Contact Boolean
_userHasPickedUp = _Newtype <<< prop (SProxy :: SProxy "userHasPickedUp")
