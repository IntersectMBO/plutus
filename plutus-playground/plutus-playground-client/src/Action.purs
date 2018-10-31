module Action where

import Bootstrap (btnLight)
import Data.Foldable (intercalate)
import Halogen.HTML (ClassName(ClassName), HTML, button, div, div_, h3_, text)
import Halogen.HTML.Properties (class_)
import Icons (Icon(..), icon)
import Prelude (pure, ($), (<$>), (<<<))
import Wallet (WalletId(WalletId), walletIdPane)

type Action =
  { walletId :: WalletId
  , name :: String
  }

actionsPane :: forall p i. Array Action -> HTML p i
actionsPane actions =
  div [ class_ $ ClassName "actions" ]
    [ h3_ [ text "Actions" ]
    , div_
      (
        intercalate
          [ icon LongArrowDown ]
          (pure <<< actionPane <$> actions)
      )
    ]

staticActions :: Array Action
staticActions =
  [ { walletId: WalletId "kris0001",  name: "Transfer" }
  , { walletId: WalletId "david0001", name: "Deposit" }
  ]

actionPane :: forall p i. Action -> HTML p i
actionPane action =
  div [ class_ $ ClassName "action" ]
    [ button [ btnLight ]
      [ div_ [ text action.name ]
      , div_ [ walletIdPane action.walletId ]
      ]
    ]
