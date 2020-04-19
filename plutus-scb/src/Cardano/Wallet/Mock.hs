{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Wallet.Mock where

import           Cardano.Wallet.Types           (WalletId)
import           Control.Lens                   (view)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error      (Error, runError, throwError)
import           Control.Monad.Freer.Extra.Log  (Log, logInfo)
import           Control.Monad.IO.Class         (MonadIO, liftIO)
import           Data.Bifunctor                 (Bifunctor (..))
import qualified Data.ByteString.Lazy           as BSL
import qualified Data.ByteString.Lazy.Char8     as BSL8
import qualified Data.Map                       as Map
import           Data.Text.Encoding             (encodeUtf8)
import           Language.Plutus.Contract.Trace (allWallets)
import           Ledger                         (Address, PubKey, TxOut (..), TxOutRef, TxOutTx (..), Value)
import           Ledger.AddressMap              (UtxoMap)
import qualified Ledger.AddressMap              as AddressMap
import           Plutus.SCB.Arbitrary           ()
import           Plutus.SCB.Utils               (tshow)
import           Servant                        (ServerError, err401, err404, err500, errBody)
import           Test.QuickCheck                (arbitrary, generate)
import           Wallet.API                     (WalletAPIError (InsufficientFunds, OtherError, PrivateKeyNotFound))
import           Wallet.Effects                 (ChainIndexEffect)
import qualified Wallet.Effects                 as W
import           Wallet.Emulator.Wallet         (Wallet (Wallet), WalletState (..))
import qualified Wallet.Emulator.Wallet         as EM

initialState :: WalletState
initialState = WalletState (EM.walletPrivKey activeWallet)

wallets :: (Member Log effs) => Eff effs [Wallet]
wallets = do
    logInfo "wallets"
    pure allWallets

fromWalletAPIError :: WalletAPIError -> ServerError
fromWalletAPIError (InsufficientFunds text) =
    err401 {errBody = BSL.fromStrict $ encodeUtf8 text}
fromWalletAPIError err@(PrivateKeyNotFound _) =
    err404 {errBody = BSL8.pack $ show err}
fromWalletAPIError (OtherError text) =
    err500 {errBody = BSL.fromStrict $ encodeUtf8 text}

valueAt ::
    ( Member Log effs
    , Member ChainIndexEffect effs
    )
    => Address
    -> Eff effs Value
valueAt address = do
    logInfo "valueAt"
    value <- foldMap (txOutValue . txOutTxOut) . view (AddressMap.fundsAt address) <$> W.watchedAddresses
    logInfo $ "valueAt " <> tshow address <> ": " <> tshow value
    pure value

selectCoin ::
    ( Member Log effs
    , Member ChainIndexEffect effs
    , Member (Error ServerError) effs
    )
    => WalletId
    -> Value
    -> Eff effs ([(TxOutRef, Value)], Value)
selectCoin walletId target = do
    logInfo "selectCoin"
    logInfo $ "  Wallet ID: " <> tshow walletId
    logInfo $ "     Target: " <> tshow target
    let address = EM.walletAddress (Wallet walletId)
    utxos :: UtxoMap <- view (AddressMap.fundsAt address) <$> W.watchedAddresses
    let funds :: [(TxOutRef, Value)]
        funds = fmap (second (txOutValue . txOutTxOut)) . Map.toList $ utxos
    result <- runM $ runError $ EM.selectCoin funds target
    logInfo $ "     Result: " <> tshow result
    case result of
        Right value -> pure value
        Left err    -> throwError $ fromWalletAPIError err

allocateAddress ::
    ( LastMember m effs
    , Member Log effs
    , MonadIO m
    )
    => WalletId
    -> Eff effs PubKey
allocateAddress _ = do
    logInfo "allocateAddress"
    sendM $ liftIO $ generate arbitrary

activeWallet :: Wallet
activeWallet = Wallet 1
