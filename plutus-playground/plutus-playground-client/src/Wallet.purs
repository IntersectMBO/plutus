module Wallet where

import Bootstrap (card, cardBody, cardTitle, col, row)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Halogen.HTML (ClassName(..), HTML, div, div_, h3_, span, strong_, text)
import Halogen.HTML.Properties (class_)
import Icons (Icon(..), icon)
import Prelude (($), (<$>))

newtype WalletId = WalletId String
derive instance newtypeWalletId :: Newtype WalletId _

type Wallet =
  { id :: WalletId
  , balance :: Number
  }

_id :: forall s a. Lens' {id :: a | s} a
_id = prop (SProxy :: SProxy "id")

_balance :: forall s a. Lens' {balance :: a | s} a
_balance = prop (SProxy :: SProxy "balance")

staticWallets :: Array Wallet
staticWallets =
  [ { id: WalletId "kris0001", balance: 10.0 }
  , { id: WalletId "kris0002", balance: 5.0 }
  , { id: WalletId "david0001", balance: 23.0 }
  , { id: WalletId "david0002", balance: 1.0 }
  , { id: WalletId "manuel0001", balance: 817.0 }
  ]

walletsPane :: forall p i. Array Wallet -> HTML p i
walletsPane wallets =
  div_
    [ h3_ [ text "Wallets" ]
    , row (walletPane <$> wallets)
    ]

walletPane :: forall p i. Wallet -> HTML p i
walletPane wallet =
  div [ class_ $ ClassName "wallet" ]
    [ card
      [ cardBody
          [ col
             [ cardTitle [ walletIdPane wallet.id ]
             , cardBody [ text "..." ]
             ]
          ]
      ]
    ]

walletIdPane :: forall p i. WalletId -> HTML p i
walletIdPane (WalletId walletId) =
  span [ class_ $ ClassName "wallet-id" ]
    [ icon CreditCard
    , text " "
    , strong_ [ text walletId ]
    ]
