module Wallet where

import Bootstrap (btn, btnGroup_, btnInfo, btnSmall, cardBody_, cardFooter_, cardTitle_, card_, col_, row_)
import Data.Newtype (unwrap)
import Halogen (HTML)
import Halogen.HTML (ClassName(ClassName), button, div, div_, h3_, span, strong_, text)
import Halogen.HTML.Events (input_, onClick)
import Halogen.HTML.Properties (class_, classes)
import Icons (Icon(..), icon)
import Prelude (show, ($), (<$>))
import StaticData (staticActionIds)
import Types (ActionId, Wallet, WalletId(WalletId), Query(..))

walletsPane :: forall p. Array Wallet -> HTML p Query
walletsPane wallets =
  div_
    [ h3_ [ text "Wallets" ]
    , row_ (walletPane <$> wallets)
    ]

walletPane :: forall p. Wallet -> HTML p Query
walletPane wallet =
  col_ [
    div [ class_ $ ClassName "wallet" ]
      [ card_
        [ cardBody_
            [ cardTitle_ [ walletIdPane wallet.walletId ]
            , div_
              [ text $ show wallet.balance
              , icon Bitcoin
              ]
            ]
        , cardFooter_
            [ btnGroup_
                (actionButton wallet.walletId <$> staticActionIds)
            ]
        ]
      ]
 ]

actionButton :: forall p. WalletId -> ActionId -> HTML p Query
actionButton walletId actionId =
  button
    [ classes [ btn, btnInfo, btnSmall ]
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
