module API.Wallet
  ( createWallet
  , submitWalletTransaction
  , getWalletInfo
  , getWalletTotalFunds
  , signTransaction
  ) where

import Prologue
import API.Request (doGetRequest, doEmptyPostRequest, doPostRequest)
import API.Url (toUrlPiece)
import Cardano.Wallet.Mock.Types (WalletInfo)
import Control.Monad.Error.Class (class MonadError)
import Effect.Aff.Class (class MonadAff)
import Plutus.V1.Ledger.Tx (Tx)
import Plutus.V1.Ledger.Value (Value)
import Servant.PureScript.Ajax (AjaxError)
import Wallet.Emulator.Wallet (Wallet)

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
