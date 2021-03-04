module WalletData.Validation
  ( NicknameError(..)
  , ContractIdError(..)
  , nicknameError
  , contractIdError
  ) where

import Prelude
import Data.Map (isEmpty, filter, member)
import Data.Maybe (Maybe(..))
import Marlowe.Semantics (PubKey)
import Network.RemoteData (RemoteData(..))
import Servant.PureScript.Ajax (AjaxError)
import WalletData.Types (Nickname, WalletLibrary)

data NicknameError
  = EmptyNickname
  | DuplicateNickname

derive instance eqNicknameError :: Eq NicknameError

instance showNicknameError :: Show NicknameError where
  show EmptyNickname = "Nickname cannot be blank"
  show DuplicateNickname = "Nickname is already in use in your contacts"

data ContractIdError
  = EmptyContractId
  | DuplicateContractId
  | UnconfirmedContractId
  | NonexistentContractId

derive instance eqKeyError :: Eq ContractIdError

instance showContracyIdError :: Show ContractIdError where
  show EmptyContractId = "Wallet ID cannot be blank"
  show DuplicateContractId = "Wallet ID is already in your contacts"
  show UnconfirmedContractId = "Looking up wallet ID..."
  show NonexistentContractId = "Wallet ID not found"

nicknameError :: Nickname -> WalletLibrary -> Maybe NicknameError
nicknameError "" _ = Just EmptyNickname

nicknameError nickname library =
  if member nickname library then
    Just DuplicateNickname
  else
    Nothing

contractIdError :: String -> RemoteData AjaxError PubKey -> WalletLibrary -> Maybe ContractIdError
contractIdError "" _ _ = Just EmptyContractId

contractIdError contractId pubKey library =
  if not $ isEmpty $ filter (\walletDetails -> walletDetails.contractId == contractId) library then
    Just DuplicateContractId
  else
    case pubKey of
      Success _ -> Nothing
      Failure _ -> Just NonexistentContractId
      _ -> Just UnconfirmedContractId

