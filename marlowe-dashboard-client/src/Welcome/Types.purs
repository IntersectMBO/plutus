module Welcome.Types
  ( State
  , Modal(..)
  , Action(..)
  , WalletNicknameOrIdError(..)
  ) where

import Prologue
import Analytics (class IsEvent, defaultEvent, toEvent)
import Clipboard (Action) as Clipboard
import Component.Modal.Types (State) as Modal
import InputField.Types (Action, State) as InputField
import InputField.Types (class InputFieldError)
import Marlowe.PAB (PlutusAppId)
import Types (WebData)
import Contacts.Types (WalletDetails, WalletLibrary, WalletNickname, WalletNicknameError)

type State
  = { modal :: Modal.State Modal
    , walletLibrary :: WalletLibrary
    , walletNicknameOrIdInput :: InputField.State WalletNicknameOrIdError
    , walletNicknameInput :: InputField.State WalletNicknameError
    , walletId :: PlutusAppId
    , remoteWalletDetails :: WebData WalletDetails
    , enteringDashboardState :: Boolean
    }

data WalletNicknameOrIdError
  = UnconfirmedWalletNicknameOrId
  | NonexistentWalletNicknameOrId

derive instance eqWalletNicknameOrIdError :: Eq WalletNicknameOrIdError

instance inputFieldErrorWalletNicknameOrIdError :: InputFieldError WalletNicknameOrIdError where
  inputErrorToString UnconfirmedWalletNicknameOrId = "Looking up wallet..."
  inputErrorToString NonexistentWalletNicknameOrId = "Wallet not found"

data Modal
  = GetStartedHelp
  | GenerateWalletHelp
  | UseNewWallet
  | UseWallet
  | LocalWalletMissing

derive instance eqModal :: Eq Modal

data Action
  = OpenModal Modal
  | CloseModal
  | GenerateWallet
  | WalletNicknameOrIdInputAction (InputField.Action WalletNicknameOrIdError)
  | OpenUseWalletModalWithDetails WalletDetails
  | WalletNicknameInputAction (InputField.Action WalletNicknameError)
  | ConnectWallet WalletNickname
  | ClearLocalStorage
  | ClipboardAction Clipboard.Action

-- | Here we decide which top-level queries to track as GA events, and how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent (OpenModal _) = Nothing
  toEvent CloseModal = Nothing
  toEvent GenerateWallet = Just $ defaultEvent "GenerateWallet"
  toEvent (WalletNicknameOrIdInputAction inputFieldAction) = toEvent inputFieldAction
  toEvent (OpenUseWalletModalWithDetails _) = Nothing
  toEvent (WalletNicknameInputAction inputFieldAction) = toEvent inputFieldAction
  toEvent (ConnectWallet _) = Just $ defaultEvent "ConnectWallet"
  toEvent ClearLocalStorage = Just $ defaultEvent "ClearLocalStorage"
  toEvent (ClipboardAction _) = Just $ defaultEvent "ClipboardAction"
