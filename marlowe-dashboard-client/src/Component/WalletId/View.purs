module Component.WalletId.View
  ( defaultInput
  , render
  ) where

import Prologue
import Component.Input.View as Input
import Component.Label.View as Label
import Component.WalletId.Types (Input)
import Data.Newtype (unwrap)
import Data.UUID (emptyUUID, toString) as UUID
import Halogen.Css (classNames)
import Halogen.HTML as HH
import Halogen.HTML.Events.Extra (onClick_)
import Marlowe.PAB (PlutusAppId(..))
import Material.Icons (icon)
import Material.Icons as Icon

defaultInput :: Input
defaultInput =
  { inputId: "walletId"
  , label: "Wallet ID"
  , value: PlutusAppId UUID.emptyUUID
  }

render :: forall w. Input -> HH.HTML w PlutusAppId
render { inputId, label, value } =
  let
    inputInput = Input.defaultInput { id = inputId, value = UUID.toString $ unwrap value }
  in
    Input.renderWithChildren inputInput \input ->
      [ Label.render Label.defaultInput { for = inputId, text = label }
      , input
      , HH.button
          [ classNames [ "cursor-pointer", "h-4", "flex", "items-center", "self-center" ]
          , onClick_ value
          ]
          [ icon Icon.Copy [ "w-6" ] ]
      ]
