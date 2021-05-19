module StaticData
  ( walletLibraryLocalStorageKey
  , walletDetailsLocalStorageKey
  , contractsLocalStorageKey
  , walletRoleContractsLocalStorageKey
  ) where

import LocalStorage (Key(..))

walletLibraryLocalStorageKey :: Key
walletLibraryLocalStorageKey = Key "walletLibrary"

walletDetailsLocalStorageKey :: Key
walletDetailsLocalStorageKey = Key "walletDetails"

contractsLocalStorageKey :: Key
contractsLocalStorageKey = Key "walletContracts"

walletRoleContractsLocalStorageKey :: Key
walletRoleContractsLocalStorageKey = Key "walletRoleContracts"
