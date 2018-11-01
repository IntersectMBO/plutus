module Wallet where

import Bootstrap (btnGroup, card, cardBody, cardTitle, col, row, btnInfoSmall)
import Data.Newtype (unwrap)
import Halogen (HTML)
import Halogen.HTML (ClassName(..), button, div, div_, h3_, span, strong_, text)
import Halogen.HTML.Events (input_, onClick)
import Halogen.HTML.Properties (class_)
import Icons (Icon(..), icon)
import Prelude (($), (<$>))
import StaticData (staticActionIds)
import Types (Action, ActionId, Wallet, WalletId(WalletId))

data Message a = Send Action a

walletsPane :: forall p. Array Wallet -> HTML p Message
walletsPane wallets =
  div_
    [ h3_ [ text "Wallets" ]
    , row (walletPane <$> wallets)
    ]

walletPane :: forall p. Wallet -> HTML p Message
walletPane wallet =
  div [ class_ $ ClassName "wallet" ]
    [ card
      [ cardBody
          [ col
             [ cardTitle [ walletIdPane wallet.walletId ]
             , div [ btnGroup ]
                 (actionButton wallet.walletId <$> staticActionIds)
             ]
          ]
      ]
    ]

actionButton :: forall p. WalletId -> ActionId -> HTML p Message
actionButton walletId actionId =
  button
    [ btnInfoSmall
    , onClick $ input_ $ Send { actionId, walletId }
    ]
    [ text (unwrap actionId) ]

walletIdPane :: forall p i. WalletId -> HTML p i
walletIdPane (WalletId walletId) =
  span [ class_ $ ClassName "wallet-id" ]
    [ icon CreditCard
    , text " "
    , strong_ [ text walletId ]
    ]
