module MainFrame.View where

import Prelude hiding (div)
import Data.Either (Either(..))
import Data.Lens (view)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import MainFrame.Lenses (_newWalletDetails, _newWalletPubKey, _templates, _subState, _wallets)
import MainFrame.Types (Action(..), ChildSlots, State)
import Pickup.View (renderPickupState)
import Play.View (renderPlayState)

render :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
render state =
  let
    wallets = view _wallets state

    newWalletDetails = view _newWalletDetails state

    newWalletPubKey = view _newWalletPubKey state

    templates = view _templates state
  in
    case view _subState state of
      Left pickupState -> PickupAction <$> renderPickupState wallets newWalletDetails newWalletPubKey pickupState
      Right playState -> PlayAction <$> renderPlayState wallets newWalletDetails newWalletPubKey templates playState
