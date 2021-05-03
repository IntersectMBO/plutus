module WalletData.State
  ( defaultWalletDetails
  , adaToken
  , getAda
  ) where

import Prelude
import Data.BigInteger (BigInteger)
import Data.Map (lookup)
import Data.Maybe (fromMaybe)
import Data.Newtype (unwrap)
import Data.UUID (emptyUUID)
import Marlowe.PAB (PlutusAppId(..))
import Marlowe.Semantics (Assets, Token(..))
import WalletData.Types (PubKeyHash(..), Wallet(..), WalletDetails, WalletInfo(..))

defaultWalletDetails :: WalletDetails
defaultWalletDetails =
  { walletNickname: mempty
  , companionAppId: PlutusAppId emptyUUID
  , walletInfo: defaultWalletInfo
  , assets: mempty
  }

defaultWalletInfo :: WalletInfo
defaultWalletInfo =
  WalletInfo
    { wallet: Wallet zero
    , pubKey: ""
    , pubKeyHash: PubKeyHash ""
    }

adaToken :: Token
adaToken = Token "" ""

getAda :: Assets -> BigInteger
getAda assets = fromMaybe zero $ lookup "" =<< lookup "" (unwrap assets)
