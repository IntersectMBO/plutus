module API.Wallet
  ( createWallet
  , submitWalletTransaction
  , getWalletInfo
  , updateWalletPaymentWithChange
  , getWalletSlot
  , getWalletTransactions
  , getWalletTotalFunds
  , signTransaction
  ) where

import Prelude
import API.Request (doGetRequest, doEmptyPostRequest, doPostRequest)
import API.Url (toUrlPiece)
import Cardano.Wallet.Types (WalletInfo)
import Control.Monad.Error.Class (class MonadError)
import Data.Json.JsonTuple (JsonTuple)
import Data.Map (Map)
import Effect.Aff.Class (class MonadAff)
import Plutus.V1.Ledger.Slot (Slot)
import Plutus.V1.Ledger.Tx (Tx, TxOutRef, TxOutTx)
import Plutus.V1.Ledger.Value (Value)
import Servant.PureScript.Ajax (AjaxError)
import Wallet.Emulator.Wallet (Wallet)
import Wallet.Types (Payment)

createWallet ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  m WalletInfo
createWallet = doEmptyPostRequest "/wallet/create"

submitWalletTransaction ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  Wallet -> Tx -> m Unit
submitWalletTransaction wallet tx = doPostRequest ("/wallet/" <> toUrlPiece wallet) tx

getWalletInfo ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  Wallet -> m WalletInfo
getWalletInfo wallet = doGetRequest ("/wallet/" <> toUrlPiece wallet <> "/own-public-key")

updateWalletPaymentWithChange ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  Wallet -> JsonTuple Value Payment -> m Payment
updateWalletPaymentWithChange wallet valuePayment = doPostRequest ("/wallet/" <> toUrlPiece wallet <> "/update-payment-with-change") valuePayment

getWalletSlot ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  Wallet -> m Slot
getWalletSlot wallet = doGetRequest $ "/wallet/" <> toUrlPiece wallet <> "/wallet-slot"

getWalletTransactions ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  Wallet -> m (Map TxOutRef TxOutTx)
getWalletTransactions wallet = doGetRequest $ "/wallet/" <> toUrlPiece wallet <> "/own-outputs"

getWalletTotalFunds ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  Wallet -> m Value
getWalletTotalFunds wallet = doGetRequest $ "/wallet/" <> toUrlPiece wallet <> "/total-funds"

signTransaction ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  Wallet -> Tx -> m Tx
signTransaction wallet tx = doPostRequest ("/wallet/" <> toUrlPiece wallet <> "/sign") tx
