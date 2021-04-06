module WalletData.Validation
  ( WalletNicknameError(..)
  , ContractInstanceIdError(..)
  , walletNicknameError
  , contractInstanceIdError
  ) where

import Prelude
import Data.Array (any)
import Data.Char.Unicode (isAlphaNum)
import Data.Map (isEmpty, filter, member)
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits (toCharArray)
import Data.UUID (parseUUID)
import MainFrame.Types (WebData)
import Marlowe.Semantics (Assets, PubKey)
import Network.RemoteData (RemoteData(..))
import WalletData.Types (ContractInstanceId(..), Wallet, WalletNickname, WalletLibrary)

data WalletNicknameError
  = EmptyWalletNickname
  | DuplicateWalletNickname
  | BadWalletNickname

derive instance eqWalletNicknameError :: Eq WalletNicknameError

instance showWalletNicknameError :: Show WalletNicknameError where
  show EmptyWalletNickname = "Nickname cannot be blank"
  show DuplicateWalletNickname = "Nickname is already in use in your contacts"
  show BadWalletNickname = "Nicknames can only contain letters and numbers"

data ContractInstanceIdError
  = EmptyContractInstanceId
  | DuplicateContractInstanceId
  | InvalidContractInstanceId
  | UnconfirmedContractInstanceId
  | NonexistentContractInstanceId

derive instance eqContractInstanceIdError :: Eq ContractInstanceIdError

instance showContractInstanceIdError :: Show ContractInstanceIdError where
  show EmptyContractInstanceId = "Wallet ID cannot be blank"
  show DuplicateContractInstanceId = "Wallet ID is already in your contacts"
  show InvalidContractInstanceId = "Wallet ID is not valid"
  show UnconfirmedContractInstanceId = "Looking up wallet ID..."
  show NonexistentContractInstanceId = "Wallet ID not found"

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

contractInstanceIdError :: String -> WebData Wallet -> WebData PubKey -> WebData Assets -> WalletLibrary -> Maybe ContractInstanceIdError
contractInstanceIdError "" _ _ _ _ = Just EmptyContractInstanceId

contractInstanceIdError contractInstanceIdString remoteDataWallet remoteDataPubKey remoteDataAssets walletLibrary = case parseContractInstanceId contractInstanceIdString of
  Nothing -> Just InvalidContractInstanceId
  Just contractInstanceId
    | not $ isEmpty $ filter (\walletDetails -> walletDetails.contractInstanceId == contractInstanceId) walletLibrary -> Just DuplicateContractInstanceId
  _ -> case remoteDataWallet, remoteDataPubKey, remoteDataAssets of
    Success _, Success _, Success _ -> Nothing
    Failure _, _, _ -> Just NonexistentContractInstanceId
    _, _, _ -> Just UnconfirmedContractInstanceId

parseContractInstanceId :: String -> Maybe ContractInstanceId
parseContractInstanceId contractInstanceIdString = case parseUUID contractInstanceIdString of
  Just uuid -> Just $ ContractInstanceId uuid
  Nothing -> Nothing
