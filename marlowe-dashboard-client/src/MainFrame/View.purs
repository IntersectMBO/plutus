module MainFrame.View where

import Prelude hiding (div)
import Data.Either (Either(..))
import Data.Lens (view)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import MainFrame.Lenses (_newWalletContractId, _newWalletNickname, _remoteDataPubKey, _templates, _subState, _wallets)
import MainFrame.Types (Action(..), ChildSlots, State)
import Pickup.View (renderPickupState)
import Play.View (renderPlayState)

render :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
render state =
  let
    wallets = view _wallets state

    newWalletNickname = view _newWalletNickname state

    newWalletContractId = view _newWalletContractId state

    remoteDataPubKey = view _remoteDataPubKey state

    templates = view _templates state
  in
    case view _subState state of
      Left pickupState -> PickupAction <$> renderPickupState wallets newWalletNickname newWalletContractId remoteDataPubKey pickupState
      Right playState -> PlayAction <$> renderPlayState wallets newWalletNickname newWalletContractId remoteDataPubKey templates playState
