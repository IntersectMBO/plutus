module Contact.Lenses
  ( _contacts
  , _newContact
  , _key
  , _nickname
  ) where

import Prelude
import Contact.Types (Contact, State, PubKeyHash)
import Data.Lens (Lens')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))

_contacts :: Lens' State (Array Contact)
_contacts = prop (SProxy :: SProxy "contacts")

_newContact :: Lens' State Contact
_newContact = prop (SProxy :: SProxy "newContact")

_key :: Lens' Contact PubKeyHash
_key = _Newtype <<< prop (SProxy :: SProxy "key")

_nickname :: Lens' Contact String
_nickname = _Newtype <<< prop (SProxy :: SProxy "nickname")
