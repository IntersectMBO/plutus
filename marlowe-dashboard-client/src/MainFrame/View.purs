module MainFrame.View where

import Prelude hiding (div)
import Css (classNames)
import Data.Either (Either(..))
import Data.Lens (view)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.HTML (div)
import MainFrame.Lenses (_newWalletDetails, _subState, _templates, _toast, _wallets)
import MainFrame.Types (Action(..), ChildSlots, State)
import Pickup.View (renderPickupState)
import Play.View (renderPlayState)
import Toast.View (renderToast)

render :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
render state =
  let
    wallets = view _wallets state

    newWalletDetails = view _newWalletDetails state

    templates = view _templates state

    toast = view _toast state
  in
    div [ classNames [ "h-full" ] ]
      [ case view _subState state of
          Left pickupState -> PickupAction <$> renderPickupState wallets newWalletDetails pickupState
          Right playState -> PlayAction <$> renderPlayState wallets newWalletDetails templates playState
      , ToastAction <$> renderToast toast
      ]
