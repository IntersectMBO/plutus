{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Wallet.Client where
import           Control.Monad.Freer
import           Control.Monad.Freer.Error (Error, throwError)
import           Wallet.Effects            (WalletEffect (..))
import           Wallet.Emulator.Error     (WalletAPIError (..))
import           Wallet.Emulator.Wallet    (Wallet (..))

handleWalletClient
    :: forall effs.
    ( Member (Error WalletAPIError) effs
    )
    => Wallet
    -> WalletEffect
    ~> Eff effs
handleWalletClient _wallet event = do
    case event of
        SubmitTxn _t           -> throwError $ OtherError "Not implemented yet"
        OwnPubKey              -> throwError $ OtherError "Not implemented yet"
        BalanceTx _utx         -> throwError $ OtherError "Not implemented yet"
        WalletAddSignature _tx -> throwError $ OtherError "Not implemented yet"
        TotalFunds             -> throwError $ OtherError "Not implemented yet"
