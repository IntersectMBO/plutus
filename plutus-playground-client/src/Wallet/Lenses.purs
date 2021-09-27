module Wallet.Lenses
  ( _simulatorWalletWallet
  , _simulatorWalletBalance
  , _walletId
  , _pubKey
  ) where

import Data.BigInteger (BigInteger)
import Data.Lens (Iso', Lens', iso)
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Playground.Types (SimulatorWallet, _SimulatorWallet)
import Plutus.V1.Ledger.Crypto (PubKey, _PubKey)
import Plutus.V1.Ledger.Value (Value)
import Prelude ((<<<))
import Wallet.Emulator.Wallet (WalletNumber, _WalletNumber)

_simulatorWalletWallet :: Lens' SimulatorWallet WalletNumber
_simulatorWalletWallet = _SimulatorWallet <<< prop (SProxy :: SProxy "simulatorWalletWallet")

_simulatorWalletBalance :: Lens' SimulatorWallet Value
_simulatorWalletBalance = _SimulatorWallet <<< prop (SProxy :: SProxy "simulatorWalletBalance")

_walletId :: Iso' WalletNumber BigInteger
_walletId = _WalletNumber <<< iso _.getWallet { getWallet: _ }

_pubKey :: Lens' PubKey String
_pubKey = _PubKey <<< prop (SProxy :: SProxy "getPubKey")
