module WalletData.Validation
  ( WalletNicknameError(..)
  , PlutusAppIdError(..)
  , walletNicknameError
  , plutusAppIdError
  , parsePlutusAppId
  ) where

import Prelude
import Data.Array (any)
import Data.Char.Unicode (isAlphaNum)
import Data.Map (isEmpty, filter, member)
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits (toCharArray)
import Data.UUID (parseUUID)
import Marlowe.PAB (PlutusAppId(..))
import Network.RemoteData (RemoteData(..))
import Types (WebData)
import WalletData.Types (WalletInfo, WalletNickname, WalletLibrary)

data WalletNicknameError
  = EmptyWalletNickname
  | DuplicateWalletNickname
  | BadWalletNickname

derive instance eqWalletNicknameError :: Eq WalletNicknameError

instance showWalletNicknameError :: Show WalletNicknameError where
  show EmptyWalletNickname = "Nickname cannot be blank"
  show DuplicateWalletNickname = "Nickname is already in use in your contacts"
  show BadWalletNickname = "Nicknames can only contain letters and numbers"

data PlutusAppIdError
  = EmptyPlutusAppId
  | DuplicatePlutusAppId
  | InvalidPlutusAppId
  | UnconfirmedPlutusAppId
  | NonexistentPlutusAppId

derive instance eqPlutusAppIdError :: Eq PlutusAppIdError

instance showPlutusAppIdError :: Show PlutusAppIdError where
  show EmptyPlutusAppId = "Wallet ID cannot be blank"
  show DuplicatePlutusAppId = "Wallet ID is already in your contacts"
  show InvalidPlutusAppId = "Wallet ID is not valid"
  show UnconfirmedPlutusAppId = "Looking up wallet ID..."
  show NonexistentPlutusAppId = "Wallet ID not found"

walletNicknameError :: WalletNickname -> WalletLibrary -> Maybe WalletNicknameError
walletNicknameError "" _ = Just EmptyWalletNickname

walletNicknameError walletNickname walletLibrary =
  if member walletNickname walletLibrary then
    Just DuplicateWalletNickname
  else
    if any (\char -> not $ isAlphaNum char) $ toCharArray walletNickname then
      Just BadWalletNickname
    else
      Nothing

plutusAppIdError :: String -> WebData WalletInfo -> WalletLibrary -> Maybe PlutusAppIdError
plutusAppIdError "" _ _ = Just EmptyPlutusAppId

plutusAppIdError plutusAppIdString remoteDataWalletInfo walletLibrary = case parsePlutusAppId plutusAppIdString of
  Nothing -> Just InvalidPlutusAppId
  Just plutusAppId
    | not $ isEmpty $ filter (\walletDetails -> walletDetails.companionAppId == plutusAppId) walletLibrary -> Just DuplicatePlutusAppId
  _ -> case remoteDataWalletInfo of
    Success _ -> Nothing
    Failure _ -> Just NonexistentPlutusAppId
    _ -> Just UnconfirmedPlutusAppId

parsePlutusAppId :: String -> Maybe PlutusAppId
parsePlutusAppId plutusAppIdString = case parseUUID plutusAppIdString of
  Just uuid -> Just $ PlutusAppId uuid
  Nothing -> Nothing
