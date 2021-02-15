module Wallet.Types
  ( WalletLibrary
  , WalletNicknameKey
  , WalletDetails(..)
  , PubKeyHash
  ) where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Newtype (class Newtype)
import Data.Tuple (Tuple)
import Foreign.Generic (class Decode, class Encode, defaultOptions, genericDecode, genericEncode)

type WalletLibrary
  = Map WalletNicknameKey WalletDetails

-- N.B. make the nickname (string) the first key so we get alphabetical ordering for free
type WalletNicknameKey
  = Tuple String PubKeyHash

newtype WalletDetails
  = WalletDetails
  { userHasPickedUp :: Boolean
  }

derive instance newtypeWalletDetails :: Newtype WalletDetails _

derive instance eqWalletDetails :: Eq WalletDetails

derive instance genericWalletDetails :: Generic WalletDetails _

instance encodeWalletDetails :: Encode WalletDetails where
  encode = genericEncode defaultOptions

instance decodeWalletDetails :: Decode WalletDetails where
  decode = genericDecode defaultOptions

-- TODO: import PubKeyHash
type PubKeyHash
  = String
