{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans  #-}
module Wallet.Emulator.SigningProcess where

import           Control.Monad             (foldM)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.State
import           Control.Monad.Freer.TH

import           Ledger                    (PubKeyHash)
import qualified Ledger                    as L
import           Ledger.Tx                 (Tx (..))
import qualified Ledger.Tx                 as Tx
import qualified Wallet.API                as WAPI
import           Wallet.Emulator.Wallet    (Wallet)
import qualified Wallet.Emulator.Wallet    as Wallet

newtype SigningProcess = SigningProcess {
    unSigningProcess :: forall effs. (Members '[Error WAPI.WalletAPIError] effs) => [L.PubKeyHash] -> Tx -> Eff effs Tx
}

-- | The default signing process is 'signWallet'
defaultSigningProcess :: Wallet -> SigningProcess
defaultSigningProcess = signWallet

-- | Sign the transaction by calling 'WAPI.signTxnWithKey' (throwing a
--   'PrivateKeyNotFound' error if called with a key other than the
--   wallet's private key)
signWallet :: Wallet -> SigningProcess
signWallet wllt = SigningProcess $
    \pks tx -> foldM (signTxnWithKey wllt) tx pks

-- | Sign the transaction with the private key of the given public
--   key. Fails if the wallet doesn't have the private key.
signTxnWithKey :: (Member (Error WAPI.WalletAPIError) r) => Wallet -> Tx -> PubKeyHash -> Eff r Tx
signTxnWithKey wllt tx pubK = do
    let ownPubK = Wallet.walletPubKey wllt
    if L.pubKeyHash ownPubK == pubK
    then pure (Wallet.signWithWallet wllt tx)
    else throwError (WAPI.PrivateKeyNotFound pubK)

-- | Sign the transaction with the private keys of the given wallets,
--   ignoring the list of public keys that the 'SigningProcess' is passed.
signWallets :: [Wallet] -> SigningProcess
signWallets wallets = SigningProcess $ \_ tx ->
    let signingKeys = Wallet.walletPrivKey <$> wallets in
    pure (foldr Tx.addSignature tx signingKeys)

instance Show SigningProcess where
    show = const "SigningProcess <...>"

data SigningProcessEffect r where
    AddSignatures :: [L.PubKeyHash] -> Tx -> SigningProcessEffect Tx
    SetSigningProcess :: SigningProcess -> SigningProcessEffect ()
makeEffect ''SigningProcessEffect

type SigningProcessEffs = '[State SigningProcess, Error WAPI.WalletAPIError]

instance (Member SigningProcessEffect effs) => WAPI.SigningProcessAPI (Eff effs) where
    addSignatures = addSignatures

handleSigningProcess
    :: (Members SigningProcessEffs effs)
    => Eff (SigningProcessEffect ': effs) ~> Eff effs
handleSigningProcess = interpret $ \case
    AddSignatures sigs tx -> do
        SigningProcess process <- get
        process sigs tx
    SetSigningProcess proc -> put proc
