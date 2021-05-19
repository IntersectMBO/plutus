module WalletData.Types
  ( WalletLibrary
  , WalletNickname
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
import Marlowe.PAB (PlutusAppId)
import Marlowe.Semantics (Assets, PubKey)

type WalletLibrary
  = Map WalletNickname WalletDetails

type WalletNickname
  = String

type WalletDetails
  = { walletNickname :: WalletNickname
    , companionAppId :: PlutusAppId
    , marloweAppId :: PlutusAppId
    , walletInfo :: WalletInfo
    , assets :: Assets
    }

-- this is the data that the wallet API returns when creating a wallet and when subsequently requesting
-- its "own-public-key"
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

-- TODO: move this into Marlowe.Semantics
newtype PubKeyHash
  = PubKeyHash String

derive instance newtypePubKeyHash :: Newtype PubKeyHash _

derive instance eqPubKeyHash :: Eq PubKeyHash

derive instance genericPubKeyHash :: Generic PubKeyHash _

instance encodePubKeyHash :: Encode PubKeyHash where
  encode value = genericEncode defaultOptions value

instance decodePubKeyHash :: Decode PubKeyHash where
  decode value = genericDecode defaultOptions value
