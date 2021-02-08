module StaticData (contactsLocalStorageKey) where

import LocalStorage (Key(..))

contactsLocalStorageKey :: Key
contactsLocalStorageKey = Key "contacts"
