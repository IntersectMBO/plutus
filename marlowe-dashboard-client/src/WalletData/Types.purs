module WalletData.Types
  ( WalletLibrary
  , WalletNickname
  , NewWalletDetails
  , WalletDetails
  , Wallet(..)
  , ContractInstanceId(..)
  ) where

import Prelude
import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.UUID (UUID, parseUUID)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Marlowe.Semantics (Assets, PubKey)
import WebData (WebData)

type WalletLibrary
  = Map WalletNickname WalletDetails

type WalletNickname
  = String

-- this is the data we have when creating a new wallet
type NewWalletDetails
  = { walletNicknameString :: String
    , contractInstanceIdString :: String
    , remoteDataWallet :: WebData Wallet
    , remoteDataPubKey :: WebData PubKey
    , remoteDataAssets :: WebData Assets
    }

-- this is the data we have for wallets that have been created
-- (we know the contractInstanceId is valid and that contract instance exists)
type WalletDetails
  = { walletNickname :: WalletNickname
    , contractInstanceId :: ContractInstanceId -- this is the ID of the wallet's companion contract instance
    , wallet :: Wallet
    , pubKey :: PubKey
    , assets :: Assets
    }

newtype Wallet
  = Wallet BigInteger

derive instance newtypeWallet :: Newtype Wallet _

derive instance eqWallet :: Eq Wallet

derive instance genericWallet :: Generic Wallet _

instance encodeWallet :: Encode Wallet where
  encode value = genericEncode defaultOptions value

instance decodeWallet :: Decode Wallet where
  decode value = genericDecode defaultOptions value

newtype ContractInstanceId
  = ContractInstanceId UUID

derive instance newtypeContractInstanceId :: Newtype ContractInstanceId _

derive instance eqContractInstanceId :: Eq ContractInstanceId

derive instance genericContractInstanceId :: Generic ContractInstanceId _

instance encodeContractInstanceId :: Encode ContractInstanceId where
  encode value = genericEncode defaultOptions value

instance decodeContractInstanceId :: Decode ContractInstanceId where
  decode value = genericDecode defaultOptions value

contractInstanceIdFromString :: String -> Maybe ContractInstanceId
contractInstanceIdFromString contractInstanceIdString = case parseUUID contractInstanceIdString of
  Just uuid -> Just $ ContractInstanceId uuid
  _ -> Nothing
