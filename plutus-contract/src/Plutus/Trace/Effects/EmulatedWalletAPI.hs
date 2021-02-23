{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeOperators    #-}
-- | Interfacing with the wallet (for making payments)
module Plutus.Trace.Effects.EmulatedWalletAPI(
    EmulatedWalletAPI(..)
    , liftWallet
    , payToWallet
    , handleEmulatedWalletAPI
    ) where

import           Control.Monad.Freer        (Eff, Member, subsume, type (~>))
import           Control.Monad.Freer.Extras (raiseEnd)
import           Control.Monad.Freer.TH     (makeEffect)
import           Ledger.Tx                  (txId)
import           Ledger.TxId                (TxId)
import           Ledger.Value               (Value)
import           Wallet.API                 (defaultSlotRange, payToPublicKey)
import           Wallet.Effects             (WalletEffect)
import qualified Wallet.Emulator            as EM
import           Wallet.Emulator.MultiAgent (MultiAgentEffect, walletAction)
import           Wallet.Emulator.Wallet     (Wallet)

data EmulatedWalletAPI r where
    LiftWallet :: Wallet -> Eff '[WalletEffect] a -> EmulatedWalletAPI a

makeEffect ''EmulatedWalletAPI

-- | Make a payment from one wallet to another
payToWallet ::
    forall effs.
    Member EmulatedWalletAPI effs
    => Wallet
    -> Wallet
    -> Value
    -> Eff effs TxId
payToWallet source target amount =
    liftWallet source $ fmap txId $ payToPublicKey defaultSlotRange amount (EM.walletPubKey target)

-- | Handle the 'EmulatedWalletAPI' effect using the emulator's
--   'MultiAgent' effect.
handleEmulatedWalletAPI ::
    Member MultiAgentEffect effs
    => EmulatedWalletAPI
    ~> Eff effs
handleEmulatedWalletAPI = \case
    LiftWallet w action ->
        walletAction w
            $ subsume
            $ raiseEnd action
