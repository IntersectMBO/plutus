module MainFrame.View where

import Prelude hiding (div)
import Css (classNames)
import Data.Either (Either(..))
import Data.Lens (view)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.HTML (div)
import MainFrame.Lenses (_currentSlot, _subState, _toast)
import MainFrame.Types (Action(..), ChildSlots, State)
import Pickup.View (renderPickupState)
import Play.View (renderPlayState)
import Toast.View (renderToast)

render :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
render state =
  let
    currentSlot = view _currentSlot state

    toast = view _toast state
  in
    div [ classNames [ "h-full" ] ]
      [ case view _subState state of
          Left pickupState -> PickupAction <$> renderPickupState pickupState
          Right playState -> PlayAction <$> renderPlayState currentSlot playState
      , ToastAction <$> renderToast toast
      ]
