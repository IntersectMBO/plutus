module Wallet.Lenses
  ( _nickname
  , _key
  , _userHasPickedUp
  ) where

import Prelude
import Data.Lens (Lens')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Lens.Tuple (_1, _2)
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Wallet.Types (PubKeyHash, WalletDetails, WalletNicknameKey)

_nickname :: Lens' WalletNicknameKey String
_nickname = _1

_key :: Lens' WalletNicknameKey PubKeyHash
_key = _2

_userHasPickedUp :: Lens' WalletDetails Boolean
_userHasPickedUp = _Newtype <<< prop (SProxy :: SProxy "userHasPickedUp")
