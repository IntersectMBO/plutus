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

submitTxn :: Tx -> ClientM ()
ownPublicKey :: ClientM PubKey
updatePaymentWithChange :: (Value, Payment) -> ClientM Payment
walletSlot :: ClientM Slot
ownOutputs :: ClientM UtxoMap
(submitTxn, ownPublicKey, updatePaymentWithChange, walletSlot, ownOutputs) =
  ( fmap void submitTxn_
  , ownPublicKey_
  , updatePaymentWithChange_
  , walletSlot_
  , ownOutputs_)
  where
    ( submitTxn_
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
  -> Eff (WalletEffect ': effs)
  ~> Eff effs
handleWalletClient clientEnv =
    let
        runClient :: forall a. ClientM a -> Eff effs a
        runClient a = (sendM $ liftIO $ runClientM a clientEnv) >>= either throwError pure
    in
      interpret $ \case
        SubmitTxn t                    -> runClient (submitTxn t)
        OwnPubKey                      -> runClient ownPublicKey
        UpdatePaymentWithChange vl pmt -> runClient $ updatePaymentWithChange (vl, pmt)
        WalletSlot                     -> runClient walletSlot
        OwnOutputs                     -> runClient ownOutputs
