module Pickup.Validation
  ( LookupWalletError(..)
  , lookupWalletNicknameError
  , lookupWalletIdError
  ) where

import Prelude
import Data.Either (Either(..))
import Data.Map (member)
import Data.Maybe (Maybe(..))
import Types (AjaxResponse)
import WalletData.Types (WalletLibrary, WalletDetails)

-- this error is for the multi-purpose input box on the pickup screen
data LookupWalletError
  = NicknameNotFound
  | LookingUpWallet
  | WalletNotFound

derive instance eqLookupWalletError :: Eq LookupWalletError

instance showLookupWalletError :: Show LookupWalletError where
  show NicknameNotFound = "Nickname not found in your wallet library"
  show LookingUpWallet = "Looking for wallet..."
  show WalletNotFound = "Wallet with this ID not found"

lookupWalletNicknameError :: WalletLibrary -> String -> Maybe LookupWalletError
lookupWalletNicknameError walletLibrary walletNickname =
  if member walletNickname walletLibrary then
    Nothing
  else
    Just NicknameNotFound

-- FIXME: use WebData and provide LookingUpWallet error for Loading case
lookupWalletIdError :: AjaxResponse WalletDetails -> String -> Maybe LookupWalletError
lookupWalletIdError (Left _) _ = Just WalletNotFound

lookupWalletIdError (Right _) _ = Nothing
