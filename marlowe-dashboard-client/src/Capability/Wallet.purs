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
import Bridge (toBack, toFront)
import Capability.Ajax (runAjax)
import Control.Monad.Except (lift)
import Data.Json.JsonTuple (JsonTuple)
import Data.Map (Map)
import Data.Newtype (unwrap)
import Halogen (HalogenM)
import MainFrame.Types (WebData)
import Marlowe.Semantics (Assets, PubKey, Slot)
import Plutus.PAB.Webserver (getWalletByWalletIdOwnoutputs, getWalletByWalletIdOwnpublickey, getWalletByWalletIdTotalfunds, getWalletByWalletIdWalletslot, postWalletByWalletIdSign, postWalletByWalletIdSubmittxn, postWalletByWalletIdUpdatepaymentwithchange, postWalletCreate)
import Plutus.V1.Ledger.Tx (Tx, TxOutRef, TxOutTx)
import Wallet.Types (Payment)
import WalletData.Types (Wallet)

-- The PAB PSGenerator (using Servant.PureScript) automatically generates a PureScript module with
-- functions for calling all Wallet API endpoints. This `MonadWallet` class wraps these up in a
-- 'capability' monad (https://thomashoneyman.com/guides/real-world-halogen/push-effects-to-the-edges/)
-- with some nicer names and type signatures, mapping the result to WebData.
class
  Monad m <= MonadWallet m where
  createWallet :: m (WebData Wallet)
  submitWalletTransaction :: Tx -> Wallet -> m (WebData Unit)
  getWalletPubKey :: Wallet -> m (WebData PubKey)
  updateWalletPaymentWithChange :: JsonTuple Assets Payment -> Wallet -> m (WebData Payment)
  getWalletSlot :: Wallet -> m (WebData Slot)
  getWalletTransactions :: Wallet -> m (WebData (Map TxOutRef TxOutTx))
  getWalletTotalFunds :: Wallet -> m (WebData Assets)
  signTransaction :: Tx -> Wallet -> m (WebData Tx)

instance monadWalletAppM :: MonadWallet AppM where
  createWallet =
    runAjax
      $ map toFront
      $ postWalletCreate
  submitWalletTransaction tx wallet =
    runAjax
      $ postWalletByWalletIdSubmittxn tx (show $ unwrap wallet)
  getWalletPubKey wallet =
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

instance monadWalletHalogenM :: MonadWallet m => MonadWallet (HalogenM state action slots msg m) where
  createWallet = lift createWallet
  submitWalletTransaction tx wallet = lift $ submitWalletTransaction tx wallet
  getWalletPubKey = lift <<< getWalletPubKey
  updateWalletPaymentWithChange valuePayment wallet = lift $ updateWalletPaymentWithChange valuePayment wallet
  getWalletSlot = lift <<< getWalletSlot
  getWalletTransactions = lift <<< getWalletTransactions
  getWalletTotalFunds = lift <<< getWalletTotalFunds
  signTransaction tx wallet = lift $ signTransaction tx wallet
