{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Cardano.Wallet.Client where

import           Cardano.Wallet.API        (API)
import           Control.Monad             (void)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error (Error, throwError)
import           Control.Monad.IO.Class    (MonadIO (..))
import           Data.Proxy                (Proxy (Proxy))
import           Ledger                    (PubKey, Value)
import           Ledger.AddressMap         (UtxoMap)
import           Ledger.Slot               (Slot)
import           Ledger.Tx                 (Tx)
import           Servant                   ((:<|>) (..))
import           Servant.Client            (ClientEnv, ClientError, ClientM, client, runClientM)
import           Wallet.Effects            (Payment (..), WalletEffect (..))
import           Wallet.Emulator.Wallet    (Wallet)

createWallet :: ClientM Wallet
submitTxn :: Wallet -> Tx -> ClientM ()
ownPublicKey :: Wallet -> ClientM PubKey
updatePaymentWithChange :: Wallet -> (Value, Payment) -> ClientM Payment
walletSlot :: Wallet -> ClientM Slot
ownOutputs :: Wallet -> ClientM UtxoMap
sign :: Wallet -> Tx -> ClientM Tx
(createWallet, submitTxn, ownPublicKey, updatePaymentWithChange, walletSlot, ownOutputs, sign) =
  ( createWallet_
  , \wid tx -> void (submitTxn_ wid tx)
  , ownPublicKey_
  , updatePaymentWithChange_
  , walletSlot_
  , ownOutputs_
  , sign_)
  where
    ( createWallet_
      :<|> (submitTxn_
      :<|> ownPublicKey_
      :<|> updatePaymentWithChange_
      :<|> walletSlot_
      :<|> ownOutputs_
      :<|> sign_)) = client (Proxy @API)

handleWalletClient ::
  forall m effs.
  ( LastMember m effs
  , MonadIO m
  , Member (Error ClientError) effs
  )
  => ClientEnv
  -> Wallet
  -> WalletEffect
  ~> Eff effs
handleWalletClient clientEnv wallet =
    let
        runClient :: forall a. ClientM a -> Eff effs a
        runClient a = (sendM $ liftIO $ runClientM a clientEnv) >>= either throwError pure
    in \case
        SubmitTxn t                    -> runClient (submitTxn wallet t)
        OwnPubKey                      -> runClient (ownPublicKey wallet)
        UpdatePaymentWithChange vl pmt -> runClient $ updatePaymentWithChange wallet (vl, pmt)
        WalletSlot                     -> runClient $ walletSlot wallet
        OwnOutputs                     -> runClient $ ownOutputs wallet
        WalletAddSignature tx          -> runClient $ sign wallet tx
