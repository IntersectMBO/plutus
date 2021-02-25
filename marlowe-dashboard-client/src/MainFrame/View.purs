module MainFrame.View where

import Prelude hiding (div)
import Data.Either (Either(..))
import Data.Lens (view)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import MainFrame.Lenses (_newWalletNicknameKey, _templates, _subState, _wallets)
import MainFrame.Types (Action(..), ChildSlots, State)
import Pickup.View (renderPickupState)
import Play.View (renderPlayState)

render :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
render state =
  let
    wallets = view _wallets state

    newWalletNicknameKey = view _newWalletNicknameKey state

    templates = view _templates state
  in
    case view _subState state of
      Left pickupState -> PickupAction <$> renderPickupState wallets newWalletNicknameKey pickupState
      Right playState -> PlayAction <$> renderPlayState wallets newWalletNicknameKey templates playState
