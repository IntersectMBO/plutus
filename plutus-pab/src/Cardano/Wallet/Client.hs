{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Cardano.Wallet.Client where

import           Cardano.Wallet.API         (API)
import           Cardano.Wallet.Types       (WalletInfo (..))
import           Control.Monad              (void)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error  (Error, throwError)
import           Control.Monad.Freer.Reader (Reader, ask)
import           Control.Monad.IO.Class     (MonadIO (..))
import           Data.Proxy                 (Proxy (Proxy))
import           Ledger                     (Value)
import           Ledger.AddressMap          (UtxoMap)
import           Ledger.Slot                (Slot)
import           Ledger.Tx                  (Tx)
import           Servant                    ((:<|>) (..))
import           Servant.Client             (ClientEnv, ClientError, ClientM, client, runClientM)
import           Wallet.Effects             (Payment (..), WalletEffect (..))
import           Wallet.Emulator.Wallet     (Wallet (..))

createWallet :: ClientM WalletInfo
submitTxn :: Wallet -> Tx -> ClientM ()
ownPublicKey :: Wallet -> ClientM WalletInfo
updatePaymentWithChange :: Wallet -> (Value, Payment) -> ClientM Payment
walletSlot :: Wallet -> ClientM Slot
ownOutputs :: Wallet -> ClientM UtxoMap
totalFunds :: Wallet -> ClientM Value
sign :: Wallet -> Tx -> ClientM Tx
(createWallet, submitTxn, ownPublicKey, updatePaymentWithChange, walletSlot, ownOutputs, totalFunds, sign) =
  ( createWallet_
  , \(Wallet wid) tx -> void (submitTxn_ wid tx)
  , ownPublicKey_ . getWallet
  , \(Wallet w) -> updatePaymentWithChange_ w
  , walletSlot_ . getWallet
  , ownOutputs_ . getWallet
  , totalFunds_ . getWallet
  , \(Wallet w) -> sign_ w)
  where
    ( createWallet_
      :<|> (submitTxn_
      :<|> ownPublicKey_
      :<|> updatePaymentWithChange_
      :<|> walletSlot_
      :<|> ownOutputs_
      :<|> totalFunds_
      :<|> sign_)) = client (Proxy @(API Integer))

handleWalletClient ::
  forall m effs.
  ( LastMember m effs
  , MonadIO m
  , Member (Error ClientError) effs
  , Member (Reader ClientEnv) effs
  )
  => Wallet
  -> WalletEffect
  ~> Eff effs
handleWalletClient wallet event = do
    clientEnv <- ask @ClientEnv
    let
        runClient :: forall a. ClientM a -> Eff effs a
        runClient a = (sendM $ liftIO $ runClientM a clientEnv) >>= either throwError pure
    case event of
        SubmitTxn t                    -> runClient (submitTxn wallet t)
        OwnPubKey                      -> wiPubKey <$> runClient (ownPublicKey wallet)
        UpdatePaymentWithChange vl pmt -> runClient $ updatePaymentWithChange wallet (vl, pmt)
        WalletSlot                     -> runClient $ walletSlot wallet
        OwnOutputs                     -> runClient $ ownOutputs wallet
        WalletAddSignature tx          -> runClient $ sign wallet tx
