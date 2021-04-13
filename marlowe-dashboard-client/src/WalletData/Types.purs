module WalletData.Types
  ( WalletLibrary
  , WalletNickname
  , NewWalletDetails
  , WalletDetails
  , WalletInfo(..)
  , Wallet(..)
  , PubKeyHash(..)
  ) where

import Prelude
import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Newtype (class Newtype)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Marlowe.Semantics (Assets, PubKey)
import Types (ContractInstanceId, WebData)

type WalletLibrary
  = Map WalletNickname WalletDetails

type WalletNickname
  = String

-- this is the data we have when creating a new wallet
type NewWalletDetails
  = { walletNicknameString :: String
    , contractInstanceIdString :: String
    , remoteDataWalletInfo :: WebData WalletInfo
    , remoteDataAssets :: WebData Assets
    }

-- this is the data we have for wallets that have been created
-- (we know the contractInstanceId is valid and that contract instance exists)
-- FIXME: the PubKey is in fact the PubKeyHash (which is what the Marlowe Plutus contract expects), so
-- we need to check whether the JSON encoding for PubKey works
type WalletDetails
  = { walletNickname :: WalletNickname
    , contractInstanceId :: ContractInstanceId -- this is the ID of the wallet's companion contract instance
    , wallet :: Wallet
    , pubKey :: PubKey
    , pubKeyHash :: PubKeyHash
    , assets :: Assets
    }

newtype WalletInfo
  = WalletInfo
  { wallet :: Wallet
  , pubKey :: PubKey
  , pubKeyHash :: PubKeyHash
  }

derive instance newtypeWalletInfo :: Newtype WalletInfo _

derive instance eqWalletInfo :: Eq WalletInfo

derive instance genericWalletInfo :: Generic WalletInfo _

instance encodeWalletInfo :: Encode WalletInfo where
  encode value = genericEncode defaultOptions value

instance decodeWalletInfo :: Decode WalletInfo where
  decode value = genericDecode defaultOptions value

newtype Wallet
  = Wallet BigInteger

derive instance newtypeWallet :: Newtype Wallet _

derive instance eqWallet :: Eq Wallet

derive instance genericWallet :: Generic Wallet _

instance encodeWallet :: Encode Wallet where
  encode value = genericEncode defaultOptions value

instance decodeWallet :: Decode Wallet where
  decode value = genericDecode defaultOptions value

newtype PubKeyHash
  = PubKeyHash String

derive instance newtypePubKeyHash :: Newtype PubKeyHash _

derive instance eqPubKeyHash :: Eq PubKeyHash

derive instance genericPubKeyHash :: Generic PubKeyHash _

instance encodePubKeyHash :: Encode PubKeyHash where
  encode value = genericEncode defaultOptions value

instance decodePubKeyHash :: Decode PubKeyHash where
  decode value = genericDecode defaultOptions value
