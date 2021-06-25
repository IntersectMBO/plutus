module MainFrame.View where

import Prelude hiding (div)
import Css (classNames)
import Data.Lens (view)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (div)
import MainFrame.Lenses (_currentSlot, _pickupState, _playState, _toast)
import MainFrame.Types (Action(..), ChildSlots, State)
import Pickup.View (renderPickupState)
import Play.View (renderPlayState)
import Toast.View (renderToast)

render :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
render state =
  let
    currentSlot = view _currentSlot state
  in
    div [ classNames [ "h-full" ] ]
      -- Before adding the tooltips (https://github.com/input-output-hk/plutus/pull/3440)
      -- this view was a case statement, selecting one subview, or the other. Now, we use
      -- the fact that _pickupState and _playState are mutually exclusive so we
      -- "render both" at the same times. Because of how renderSubmodule works, if
      -- the lens is not pointing at anything, an empty div will be drawn instead.
      [ renderSubmodule _pickupState PickupAction renderPickupState state
      , renderSubmodule _playState PlayAction (renderPlayState currentSlot) state
      , renderSubmodule _toast ToastAction renderToast state
      ]
