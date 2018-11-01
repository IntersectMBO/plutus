module Wallet where

import Bootstrap (btnGroup, btnInfoSmall, card, cardBody, cardFooter, cardTitle, col, row)
import Data.Newtype (unwrap)
import Halogen (HTML)
import Halogen.HTML (ClassName(ClassName), button, div, div_, h3_, span, strong_, text)
import Halogen.HTML.Events (input_, onClick)
import Halogen.HTML.Properties (class_)
import Icons (Icon(..), icon)
import Prelude (show, ($), (<$>))
import StaticData (staticActionIds)
import Types (ActionId, Wallet, WalletId(WalletId), Query(..))

walletsPane :: forall p. Array Wallet -> HTML p Query
walletsPane wallets =
  div_
    [ h3_ [ text "Wallets" ]
    , row (walletPane <$> wallets)
    ]

walletPane :: forall p. Wallet -> HTML p Query
walletPane wallet =
  div [ class_ $ ClassName "wallet" ]
    [ card
      [ cardBody
          [ col
             [ cardTitle [ walletIdPane wallet.walletId ]
             , div_
               [ text $ show wallet.balance
               , icon Bitcoin
               ]
             ]
          ]
      , cardFooter
          [ div [ btnGroup ]
              (actionButton wallet.walletId <$> staticActionIds)
          ]
      ]
    ]

actionButton :: forall p. WalletId -> ActionId -> HTML p Query
actionButton walletId actionId =
  button
    [ btnInfoSmall
    , onClick $ input_ $ SendAction { actionId, walletId }
    ]
    [ text (unwrap actionId) ]

walletIdPane :: forall p i. WalletId -> HTML p i
walletIdPane (WalletId walletId) =
  span [ class_ $ ClassName "wallet-id" ]
    [ icon CreditCard
    , text " "
    , strong_ [ text walletId ]
    ]
