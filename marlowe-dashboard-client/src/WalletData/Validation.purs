module WalletData.Validation
  ( WalletNicknameOrIdError(..)
  , walletNicknameOrIdError
  , WalletNicknameError(..)
  , walletNicknameError
  , WalletIdError(..)
  , walletIdError
  , parsePlutusAppId
  ) where

import Prelude
import Data.Array (any)
import Data.Char.Unicode (isAlphaNum)
import Data.Map (isEmpty, filter, member)
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits (toCharArray)
import Data.UUID (parseUUID)
import InputField.Types (class InputFieldError)
import Marlowe.PAB (PlutusAppId(..))
import Network.RemoteData (RemoteData(..))
import Types (WebData)
import WalletData.Types (WalletInfo, WalletLibrary, WalletNickname, WalletDetails)

data WalletNicknameOrIdError
  = UnconfirmedWalletNicknameOrId
  | NonexistentWalletNicknameOrId

derive instance eqWalletNicknameOrIdError :: Eq WalletNicknameOrIdError

instance inputFieldErrorWalletNicknameOrIdError :: InputFieldError WalletNicknameOrIdError where
  inputErrorToString UnconfirmedWalletNicknameOrId = "Looking up wallet..."
  inputErrorToString NonexistentWalletNicknameOrId = "Wallet not found"

walletNicknameOrIdError :: WebData WalletDetails -> String -> Maybe WalletNicknameOrIdError
walletNicknameOrIdError remoteWalletDetails _ = case remoteWalletDetails of
  Loading -> Just UnconfirmedWalletNicknameOrId
  Failure _ -> Just NonexistentWalletNicknameOrId
  _ -> Nothing

data WalletNicknameError
  = EmptyWalletNickname
  | DuplicateWalletNickname
  | BadWalletNickname

derive instance eqWalletNicknameError :: Eq WalletNicknameError

instance inputFieldErrorWalletNicknameError :: InputFieldError WalletNicknameError where
  inputErrorToString EmptyWalletNickname = "Nickname cannot be blank"
  inputErrorToString DuplicateWalletNickname = "Nickname is already in use in your contacts"
  inputErrorToString BadWalletNickname = "Nicknames can only contain letters and numbers"

walletNicknameError :: WalletLibrary -> WalletNickname -> Maybe WalletNicknameError
walletNicknameError _ "" = Just EmptyWalletNickname

walletNicknameError walletLibrary walletNickname =
  if member walletNickname walletLibrary then
    Just DuplicateWalletNickname
  else
    if any (\char -> not $ isAlphaNum char) $ toCharArray walletNickname then
      Just BadWalletNickname
    else
      Nothing

data WalletIdError
  = EmptyWalletId
  | DuplicateWalletId
  | InvalidWalletId
  | UnconfirmedWalletId
  | NonexistentWalletId

derive instance eqWalletIdError :: Eq WalletIdError

instance inputeFieldErrorWalletIdError :: InputFieldError WalletIdError where
  inputErrorToString EmptyWalletId = "Wallet ID cannot be blank"
  inputErrorToString DuplicateWalletId = "Wallet ID is already in your contacts"
  inputErrorToString InvalidWalletId = "Wallet ID is not valid"
  inputErrorToString UnconfirmedWalletId = "Looking up wallet..."
  inputErrorToString NonexistentWalletId = "Wallet not found"

walletIdError :: WebData WalletInfo -> WalletLibrary -> String -> Maybe WalletIdError
walletIdError _ _ "" = Just EmptyWalletId

walletIdError remoteDataWalletInfo walletLibrary walletIdString = case parsePlutusAppId walletIdString of
  Nothing -> Just InvalidWalletId
  Just plutusAppId
    | not $ isEmpty $ filter (\walletDetails -> walletDetails.companionAppId == plutusAppId) walletLibrary -> Just DuplicateWalletId
  _ -> case remoteDataWalletInfo of
    Success _ -> Nothing
    Failure _ -> Just NonexistentWalletId
    _ -> Just UnconfirmedWalletId

parsePlutusAppId :: String -> Maybe PlutusAppId
parsePlutusAppId plutusAppIdString = case parseUUID plutusAppIdString of
  Just uuid -> Just $ PlutusAppId uuid
  Nothing -> Nothing
