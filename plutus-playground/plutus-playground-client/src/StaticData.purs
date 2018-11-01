module StaticData where

import Types

staticWallets :: Array Wallet
staticWallets =
  [ { walletId: WalletId "kris0001", balance: 10.0 }
  , { walletId: WalletId "kris0002", balance: 5.0 }
  , { walletId: WalletId "david0001", balance: 23.0 }
  , { walletId: WalletId "david0002", balance: 1.0 }
  , { walletId: WalletId "manuel0001", balance: 817.0 }
  ]

staticActionIds :: Array ActionId
staticActionIds =
  [ ActionId "Deposit"
  , ActionId "Transfer"
  , ActionId "Collect"
  ]
