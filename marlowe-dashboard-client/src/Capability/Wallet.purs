module Capability.Wallet
  ( class MonadWallet
  , createWallet
  , submitWalletTransaction
  , getWalletPubKey
  , updateWalletPaymentWithChange
  , getWalletSlot
  , getWalletTransactions
  , getWalletTotalFunds
  , signTransaction
  ) where

import Prelude
import AppM (AppM)
import Capability.Ajax (WebData, runAjax)
import Control.Monad.Except (lift)
import Data.Json.JsonTuple (JsonTuple)
import Data.Lens (view)
import Data.Map (Map)
import Halogen (HalogenM)
import Plutus.PAB.Webserver (getWalletByWalletIdOwnoutputs, getWalletByWalletIdOwnpublickey, getWalletByWalletIdTotalfunds, getWalletByWalletIdWalletslot, postWalletByWalletIdSign, postWalletByWalletIdSubmittxn, postWalletByWalletIdUpdatepaymentwithchange, postWalletCreate)
import Plutus.V1.Ledger.Crypto (PubKey)
import Plutus.V1.Ledger.Slot (Slot)
import Plutus.V1.Ledger.Tx (Tx, TxOutRef, TxOutTx)
import Plutus.V1.Ledger.Value (Value)
import Wallet.Emulator.Wallet (Wallet)
import Wallet.Types (Payment)
import WalletData.Lenses (_getWallet)

-- The PAB PSGenerator (using Servant.PureScript) automatically generates a PureScript module with
-- functions for calling all Wallet API endpoints. This `MonadContract` class wraps these up in a
-- 'capability' monad (https://thomashoneyman.com/guides/real-world-halogen/push-effects-to-the-edges/)
-- with some nicer names, and mapping the result to RemoteData.
class
  Monad m <= MonadWallet m where
  createWallet :: m (WebData Wallet)
  submitWalletTransaction :: Tx -> Wallet -> m (WebData Unit)
  getWalletPubKey :: Wallet -> m (WebData PubKey)
  updateWalletPaymentWithChange :: JsonTuple Value Payment -> Wallet -> m (WebData Payment)
  getWalletSlot :: Wallet -> m (WebData Slot)
  getWalletTransactions :: Wallet -> m (WebData (Map TxOutRef TxOutTx))
  getWalletTotalFunds :: Wallet -> m (WebData Value)
  signTransaction :: Tx -> Wallet -> m (WebData Tx)

instance monadWalletAppM :: MonadWallet AppM where
  createWallet = runAjax postWalletCreate
  submitWalletTransaction tx wallet = runAjax $ postWalletByWalletIdSubmittxn tx wallet
  getWalletPubKey wallet = runAjax $ getWalletByWalletIdOwnpublickey wallet
  updateWalletPaymentWithChange valuePayment wallet = runAjax $ postWalletByWalletIdUpdatepaymentwithchange valuePayment wallet
  getWalletSlot wallet = runAjax $ getWalletByWalletIdWalletslot wallet
  getWalletTransactions wallet = runAjax $ getWalletByWalletIdOwnoutputs wallet
  getWalletTotalFunds wallet = runAjax $ getWalletByWalletIdTotalfunds (show $ view _getWallet wallet)
  signTransaction tx wallet = runAjax $ postWalletByWalletIdSign tx wallet

instance monadWalletHalogenM :: MonadWallet m => MonadWallet (HalogenM state action slots msg m) where
  createWallet = lift createWallet
  submitWalletTransaction tx wallet = lift $ submitWalletTransaction tx wallet
  getWalletPubKey = lift <<< getWalletPubKey
  updateWalletPaymentWithChange valuePayment wallet = lift $ updateWalletPaymentWithChange valuePayment wallet
  getWalletSlot = lift <<< getWalletSlot
  getWalletTransactions = lift <<< getWalletTransactions
  getWalletTotalFunds = lift <<< getWalletTotalFunds
  signTransaction tx wallet = lift $ signTransaction tx wallet
