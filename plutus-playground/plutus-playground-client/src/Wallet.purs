module Wallet where

import Bootstrap (btn, btnGroup_, btnInfo, btnLight, btnSmall, card, cardBody_, cardFooter_, cardHeader_, cardTitle_, card_, col_, col2_, pullRight, row_)
import Data.Array (mapWithIndex)
import Data.Array as Array
import Data.Newtype (unwrap)
import Halogen (HTML)
import Halogen.HTML (ClassName(ClassName), button, div, div_, h3_, span, strong_, text)
import Halogen.HTML.Events (input_, onClick)
import Halogen.HTML.Properties (class_, classes)
import Icons (Icon(..), icon)
import Prelude (($), (<$>), show)
import StaticData as Static
import Types (ActionId, Query(..), Wallet, WalletId(WalletId))

walletsPane :: forall p. Array Wallet -> HTML p Query
walletsPane wallets =
  div_
    [ h3_ [ text "Wallets" ]
    , row_ (Array.cons addWalletPane (mapWithIndex walletPane wallets))
    ]

walletPane :: forall p. Int -> Wallet -> HTML p Query
walletPane index wallet =
  col_
    [ div
        [class_ $ ClassName "wallet"]
        [ card_
            [ cardBody_
                [ button
                    [ classes [ btn, pullRight ]
                    , onClick $ input_ $ RemoveWallet index
                    ]
                    [ icon Close ]
                , cardTitle_ [walletIdPane wallet . walletId]
                , div_ [text $ show wallet . balance, icon Bitcoin]
                ]
            , cardFooter_
                [ btnGroup_
                    (actionButton wallet . walletId <$> Static.actionIds)
                ]
            ]
        ]
    ]

addWalletPane :: forall p. HTML p Query
addWalletPane =
  col2_
    [ div
        [ class_ $ ClassName "add-wallet" ]
        [ div [ class_ card
              , onClick $ input_ AddWallet
              ]
            [ cardBody_
                [ icon Plus ]
            ]
        ]
    ]

actionButton :: forall p. WalletId -> ActionId -> HTML p Query
actionButton walletId actionId =
  button
    [ classes [ btn, btnInfo, btnSmall ]
    , onClick $ input_ $ SendAction { actionId, walletId }
    ]
    [ text $ unwrap actionId ]

walletIdPane :: forall p i. WalletId -> HTML p i
walletIdPane (WalletId walletId) =
  span [ class_ $ ClassName "wallet-id" ]
    [ icon CreditCard
    , text " "
    , strong_ [ text walletId ]
    ]
