module StaticData
  ( walletsLocalStorageKey
  , walletLocalStorageKey
  ) where

import LocalStorage (Key(..))

walletsLocalStorageKey :: Key
walletsLocalStorageKey = Key "wallets"

walletLocalStorageKey :: Key
walletLocalStorageKey = Key "wallet"
