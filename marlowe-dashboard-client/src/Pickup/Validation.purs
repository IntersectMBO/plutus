module Pickup.Validation
  ( WalletNicknameOrIdError(..)
  , walletNicknameError
  , walletIdError
  ) where

import Prelude
import Data.Either (Either(..))
import Data.Map (member)
import Data.Maybe (Maybe(..))
import Types (AjaxResponse)
import WalletData.Types (WalletLibrary, WalletDetails)

data WalletNicknameOrIdError
  = NicknameNotFound
  | WalletNotFound

derive instance eqWalletNicknameOrIdError :: Eq WalletNicknameOrIdError

instance showWalletNicknameOrIdError :: Show WalletNicknameOrIdError where
  show NicknameNotFound = "Nickname not found in your wallet library"
  show WalletNotFound = "Wallet with this ID not found"

walletNicknameError :: WalletLibrary -> String -> Maybe WalletNicknameOrIdError
walletNicknameError walletLibrary walletNickname =
  if member walletNickname walletLibrary then
    Nothing
  else
    Just NicknameNotFound

walletIdError :: AjaxResponse WalletDetails -> String -> Maybe WalletNicknameOrIdError
walletIdError (Left _) _ = Just WalletNotFound

walletIdError (Right _) _ = Nothing
