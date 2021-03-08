module StaticData
  ( walletLibraryLocalStorageKey
  , walletDetailsLocalStorageKey
  ) where

import LocalStorage (Key(..))

walletLibraryLocalStorageKey :: Key
walletLibraryLocalStorageKey = Key "walletLibrary"

walletDetailsLocalStorageKey :: Key
walletDetailsLocalStorageKey = Key "walletDetails"
