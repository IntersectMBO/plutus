module Capability.Wallet
  ( class ManageWallet
  , createWallet
  , submitWalletTransaction
  , getWalletInfo
  , updateWalletPaymentWithChange
  , getWalletSlot
  , getWalletTransactions
  , getWalletTotalFunds
  , signTransaction
  ) where

import Prelude
import API.Wallet as API
import AppM (AppM)
import Bridge (toBack, toFront)
import Control.Monad.Except (lift, runExceptT)
import Data.Json.JsonTuple (JsonTuple)
import Data.Map (Map)
import Halogen (HalogenM)
import Marlowe.Semantics (Assets, Slot)
import Plutus.V1.Ledger.Tx (Tx, TxOutRef, TxOutTx)
import Types (AjaxResponse)
import Wallet.Types (Payment)
import WalletData.Types (Wallet, WalletInfo)

class
  Monad m <= ManageWallet m where
  createWallet :: m (AjaxResponse WalletInfo)
  submitWalletTransaction :: Wallet -> Tx -> m (AjaxResponse Unit)
  getWalletInfo :: Wallet -> m (AjaxResponse WalletInfo)
  updateWalletPaymentWithChange :: Wallet -> JsonTuple Assets Payment -> m (AjaxResponse Payment)
  getWalletSlot :: Wallet -> m (AjaxResponse Slot)
  getWalletTransactions :: Wallet -> m (AjaxResponse (Map TxOutRef TxOutTx))
  getWalletTotalFunds :: Wallet -> m (AjaxResponse Assets)
  signTransaction :: Wallet -> Tx -> m (AjaxResponse Tx)

instance monadWalletAppM :: ManageWallet AppM where
  createWallet = map toFront $ runExceptT $ API.createWallet
  submitWalletTransaction wallet tx = runExceptT $ API.submitWalletTransaction (toBack wallet) tx
  getWalletInfo wallet = map toFront $ runExceptT $ API.getWalletInfo (toBack wallet)
  updateWalletPaymentWithChange wallet valuePayment = runExceptT $ API.updateWalletPaymentWithChange (toBack wallet) (toBack valuePayment)
  getWalletSlot wallet = map toFront $ runExceptT $ API.getWalletSlot (toBack wallet)
  getWalletTransactions wallet = runExceptT $ API.getWalletTransactions (toBack wallet)
  getWalletTotalFunds wallet = map toFront $ runExceptT $ API.getWalletTotalFunds (toBack wallet)
  signTransaction wallet tx = runExceptT $ API.signTransaction (toBack wallet) tx

instance monadWalletHalogenM :: ManageWallet m => ManageWallet (HalogenM state action slots msg m) where
  createWallet = lift createWallet
  submitWalletTransaction tx wallet = lift $ submitWalletTransaction tx wallet
  getWalletInfo = lift <<< getWalletInfo
  updateWalletPaymentWithChange valuePayment wallet = lift $ updateWalletPaymentWithChange valuePayment wallet
  getWalletSlot = lift <<< getWalletSlot
  getWalletTransactions = lift <<< getWalletTransactions
  getWalletTotalFunds = lift <<< getWalletTotalFunds
  signTransaction tx wallet = lift $ signTransaction tx wallet
