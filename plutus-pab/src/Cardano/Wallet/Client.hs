{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Cardano.Wallet.Client where

import           Cardano.Wallet.API        (API)
import           Cardano.Wallet.Types
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

createWallet :: ClientM Integer
submitTxn :: Integer -> Tx -> ClientM ()
ownPublicKey :: Integer -> ClientM PubKey
updatePaymentWithChange :: Integer -> (Value, Payment) -> ClientM Payment
walletSlot :: Integer -> ClientM Slot
ownOutputs :: Integer -> ClientM UtxoMap
(createWallet, submitTxn, ownPublicKey, updatePaymentWithChange, walletSlot, ownOutputs) =
  ( createWallet_
  , \wid tx -> void (submitTxn_ wid tx)
  , ownPublicKey_
  , updatePaymentWithChange_
  , walletSlot_
  , ownOutputs_)
  where
    ( createWallet_
      :<|> submitTxn_
      :<|> ownPublicKey_
      :<|> updatePaymentWithChange_
      :<|> walletSlot_
      :<|> ownOutputs_) = client (Proxy @API)

handleWalletClient ::
  forall m effs.
  ( LastMember m effs
  , MonadIO m
  , Member (Error ClientError) effs
  )
  => ClientEnv
  -> WalletId
  -> Eff (WalletEffect ': effs)
  ~> Eff effs
handleWalletClient clientEnv walletId =
    let
        runClient :: forall a. ClientM a -> Eff effs a
        runClient a = (sendM $ liftIO $ runClientM a clientEnv) >>= either throwError pure
    in
      interpret $ \case
        SubmitTxn t                    -> runClient (submitTxn walletId t)
        OwnPubKey                      -> runClient (ownPublicKey walletId)
        UpdatePaymentWithChange vl pmt -> runClient $ updatePaymentWithChange walletId (vl, pmt)
        WalletSlot                     -> runClient $ walletSlot walletId
        OwnOutputs                     -> runClient $ ownOutputs walletId
