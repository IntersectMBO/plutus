module Wallet.Lenses
  ( _nickname
  , _key
  , _userHasPickedUp
  ) where

import Data.Lens (Lens')
import Data.Lens.Lens.Tuple (_1, _2)
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Marlowe.Semantics (PubKey)
import Wallet.Types (WalletDetails, WalletNicknameKey)

_nickname :: Lens' WalletNicknameKey String
_nickname = _1

_key :: Lens' WalletNicknameKey PubKey
_key = _2

_userHasPickedUp :: Lens' WalletDetails Boolean
_userHasPickedUp = prop (SProxy :: SProxy "userHasPickedUp")
