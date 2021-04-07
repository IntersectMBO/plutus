module WalletData.Types
  ( WalletLibrary
  , WalletNickname
  , NewWalletDetails
  , WalletDetails
  , Wallet(..)
  ) where

import Prelude
import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Newtype (class Newtype)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Marlowe.Semantics (Assets, PubKey)
import Marlowe.Types (ContractInstanceId)
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
