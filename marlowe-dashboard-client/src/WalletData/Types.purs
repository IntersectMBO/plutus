module WalletData.Types
  ( WalletLibrary
  , WalletNickname
  , NewWalletDetails
  , WalletDetails
  ) where

import Data.Map (Map)
import Network.RemoteData (RemoteData)
import Plutus.V1.Ledger.Crypto (PubKey)
import Plutus.V1.Ledger.Value (Value)
import Servant.PureScript.Ajax (AjaxError)
import Wallet.Emulator.Wallet (Wallet)
import Wallet.Types (ContractInstanceId)

type WalletLibrary
  = Map WalletNickname WalletDetails

type WalletNickname
  = String

-- this is the data we have when creating a new wallet
type NewWalletDetails
  = { walletNicknameString :: String
    , contractInstanceIdString :: String
    , remoteDataWallet :: RemoteData AjaxError Wallet
    , remoteDataPubKey :: RemoteData AjaxError PubKey
    , remoteDataValue :: RemoteData AjaxError Value
    }

-- this is the data we have for wallets that have been created
-- (we know the contractInstanceId is valid and that contract instance exists)
type WalletDetails
  = { walletNickname :: WalletNickname
    , contractInstanceId :: ContractInstanceId -- this is the ID of the wallet's companion contract instance
    , wallet :: Wallet
    , pubKey :: PubKey
    , value :: Value
    }
