module WalletData.State (defaultWalletDetails) where

import Prelude
import Data.UUID (emptyUUID)
import Marlowe.PAB (ContractInstanceId(..))
import WalletData.Types (PubKeyHash(..), Wallet(..), WalletDetails, WalletInfo(..))

defaultWalletDetails :: WalletDetails
defaultWalletDetails =
  { walletNickname: mempty
  , marloweContractId: ContractInstanceId emptyUUID
  , companionContractId: ContractInstanceId emptyUUID
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
