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
import AppM (AppM)
import Bridge (toBack, toFront)
import Capability.Ajax (runAjax)
import Control.Monad.Except (lift)
import Data.Json.JsonTuple (JsonTuple)
import Data.Map (Map)
import Data.Newtype (unwrap)
import Halogen (HalogenM)
import Marlowe.Semantics (Assets, Slot)
import Plutus.PAB.Webserver (getWalletByWalletIdOwnoutputs, getWalletByWalletIdOwnpublickey, getWalletByWalletIdTotalfunds, getWalletByWalletIdWalletslot, postWalletByWalletIdSign, postWalletByWalletIdSubmittxn, postWalletByWalletIdUpdatepaymentwithchange, postWalletCreate)
import Plutus.V1.Ledger.Tx (Tx, TxOutRef, TxOutTx)
import Types (WebData)
import Wallet.Types (Payment)
import WalletData.Types (Wallet, WalletInfo)

-- The PAB PSGenerator (using Servant.PureScript) automatically generates a PureScript module with
-- functions for calling all Wallet API endpoints. This `ManageWallet` class wraps these up in a
-- 'capability' monad (https://thomashoneyman.com/guides/real-world-halogen/push-effects-to-the-edges/)
-- with some nicer names and type signatures, mapping the result to WebData.
class
  Monad m <= ManageWallet m where
  createWallet :: m (WebData WalletInfo)
  submitWalletTransaction :: Tx -> Wallet -> m (WebData Unit)
  getWalletInfo :: Wallet -> m (WebData WalletInfo)
  updateWalletPaymentWithChange :: JsonTuple Assets Payment -> Wallet -> m (WebData Payment)
  getWalletSlot :: Wallet -> m (WebData Slot)
  getWalletTransactions :: Wallet -> m (WebData (Map TxOutRef TxOutTx))
  getWalletTotalFunds :: Wallet -> m (WebData Assets)
  signTransaction :: Tx -> Wallet -> m (WebData Tx)

instance monadWalletAppM :: ManageWallet AppM where
  createWallet =
    runAjax
      $ map toFront
      $ postWalletCreate
  submitWalletTransaction tx wallet =
    runAjax
      $ postWalletByWalletIdSubmittxn tx (show $ unwrap wallet)
  getWalletInfo wallet =
    runAjax
      $ map toFront
      $ getWalletByWalletIdOwnpublickey (show $ unwrap wallet)
  updateWalletPaymentWithChange valuePayment wallet =
    runAjax
      $ postWalletByWalletIdUpdatepaymentwithchange (toBack valuePayment) (show $ unwrap wallet)
  getWalletSlot wallet =
    runAjax
      $ map toFront
      $ getWalletByWalletIdWalletslot (show $ unwrap wallet)
  getWalletTransactions wallet =
    runAjax
      $ getWalletByWalletIdOwnoutputs (show $ unwrap wallet)
  getWalletTotalFunds wallet =
    runAjax
      $ map toFront
      $ getWalletByWalletIdTotalfunds (show $ unwrap wallet)
  signTransaction tx wallet =
    runAjax
      $ postWalletByWalletIdSign tx (show $ unwrap wallet)

instance monadWalletHalogenM :: ManageWallet m => ManageWallet (HalogenM state action slots msg m) where
  createWallet = lift createWallet
  submitWalletTransaction tx wallet = lift $ submitWalletTransaction tx wallet
  getWalletInfo = lift <<< getWalletInfo
  updateWalletPaymentWithChange valuePayment wallet = lift $ updateWalletPaymentWithChange valuePayment wallet
  getWalletSlot = lift <<< getWalletSlot
  getWalletTransactions = lift <<< getWalletTransactions
  getWalletTotalFunds = lift <<< getWalletTotalFunds
  signTransaction tx wallet = lift $ signTransaction tx wallet
