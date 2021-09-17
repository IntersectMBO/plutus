module Web.Common.Components.WalletId
  ( Params
  , defaultParams
  , render
  ) where

import Prelude
import Data.Newtype (unwrap)
import Data.UUID (emptyUUID, toString) as UUID
import Halogen.Css (classNames)
import Halogen.HTML as HH
import Halogen.HTML.Events.Extra (onClick_)
import Marlowe.PAB (PlutusAppId(..))
import Material.Icons (icon)
import Material.Icons as Icon
import Web.Common.Components.Input as Input
import Web.Common.Components.Label as Label

-------------------------------------------------------------------------------
-- Public API types
-------------------------------------------------------------------------------
type Params
  = { inputId :: String
    , label :: String
    , value :: PlutusAppId
    }

-------------------------------------------------------------------------------
-- Public API
-------------------------------------------------------------------------------
defaultParams :: Params
defaultParams =
  { inputId: "walletId"
  , label: "Wallet ID"
  , value: PlutusAppId UUID.emptyUUID
  }

render :: forall w. Params -> HH.HTML w PlutusAppId
render { inputId, label, value } =
  let
    inputParams = Input.defaultParams { id = inputId, value = UUID.toString $ unwrap value }
  in
    Input.renderWithChildren inputParams \input ->
      [ Label.render Label.defaultParams { for = inputId, text = label }
      , input
      , HH.button
          [ classNames [ "cursor-pointer", "h-4", "flex", "items-center", "self-center" ]
          , onClick_ value
          ]
          [ icon Icon.Copy [ "w-6" ] ]
      ]
