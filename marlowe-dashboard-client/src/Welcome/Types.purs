module Welcome.Types
  ( State
  , Card(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Data.Maybe (Maybe(..))
import InputField.Types (Action, State) as InputField
import Types (WebData)
import WalletData.Types (WalletDetails, WalletLibrary, WalletNickname)
import WalletData.Validation (WalletIdError, WalletNicknameError, WalletNicknameOrIdError)

type State
  = { card :: Maybe Card
    , walletLibrary :: WalletLibrary
    , walletNicknameOrIdInput :: InputField.State WalletNicknameOrIdError
    , walletNicknameInput :: InputField.State WalletNicknameError
    , walletIdInput :: InputField.State WalletIdError
    , remoteWalletDetails :: WebData WalletDetails
    , connecting :: Boolean -- true when we are in the process of connecting a wallet
    }

data Card
  = GetStartedHelpCard
  | GenerateWalletHelpCard
  | ConnectNewWalletCard
  | ConnectWalletCard
  | LocalWalletMissingCard

derive instance eqCard :: Eq Card

data Action
  = OpenCard Card
  | CloseCard Card
  | GenerateWallet
  | WalletNicknameOrIdInputAction (InputField.Action WalletNicknameOrIdError)
  | OpenConnectWalletCardWithDetails WalletDetails
  | WalletNicknameInputAction (InputField.Action WalletNicknameError)
  | WalletIdInputAction (InputField.Action WalletIdError)
  | ConnectWallet WalletNickname
  | ClearLocalStorage

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent (OpenCard _) = Nothing
  toEvent (CloseCard _) = Nothing
  toEvent GenerateWallet = Just $ defaultEvent "GenerateWallet"
  toEvent (WalletNicknameOrIdInputAction inputFieldAction) = toEvent inputFieldAction
  toEvent (OpenConnectWalletCardWithDetails _) = Nothing
  toEvent (WalletNicknameInputAction inputFieldAction) = toEvent inputFieldAction
  toEvent (WalletIdInputAction inputFieldAction) = toEvent inputFieldAction
  toEvent (ConnectWallet _) = Just $ defaultEvent "ConnectWallet"
  toEvent ClearLocalStorage = Just $ defaultEvent "ClearLocalStorage"
