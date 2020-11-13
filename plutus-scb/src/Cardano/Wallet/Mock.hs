{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Wallet.Mock where

import           Cardano.Wallet.Types           (WalletId)
import           Control.Lens                   (view)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error      (Error, runError, throwError)
import           Control.Monad.Freer.Log        (LogMsg, logInfo)
import           Control.Monad.IO.Class         (MonadIO, liftIO)
import           Data.Bifunctor                 (Bifunctor (..))
import qualified Data.ByteString.Lazy           as BSL
import qualified Data.ByteString.Lazy.Char8     as BSL8
import qualified Data.Map                       as Map
import           Data.Text.Encoding             (encodeUtf8)
import           Data.Text.Prettyprint.Doc      (Pretty (..), (<+>))
import           Language.Plutus.Contract.Trace (allWallets)
import           Ledger                         (Address, PubKey, TxOut (..), TxOutRef, TxOutTx (..), Value)
import           Ledger.AddressMap              (UtxoMap)
import qualified Ledger.AddressMap              as AddressMap
import           Plutus.SCB.Arbitrary           ()
import           Servant                        (ServerError, err401, err404, err500, errBody)
import           Test.QuickCheck                (arbitrary, generate)
import           Wallet.API                     (WalletAPIError (InsufficientFunds, OtherError, PrivateKeyNotFound))
import           Wallet.Effects                 (ChainIndexEffect)
import qualified Wallet.Effects                 as W
import           Wallet.Emulator.Wallet         (Wallet (Wallet), WalletState (..))
import qualified Wallet.Emulator.Wallet         as EM

initialState :: Wallet -> WalletState
initialState = WalletState . EM.walletPrivKey

data MockWalletMsg =
    CallWallets
    | CallValueAt
    | ValueAtResponse Address Value
    | CallSelectCoin WalletId Value
    | SelectCoinResult (Either WalletAPIError ([(TxOutRef, Value)], Value))
    | CallAllocateAddress

instance Pretty MockWalletMsg where
    pretty = \case
        CallWallets                    -> "wallets"
        CallValueAt                    -> "valueAt"
        ValueAtResponse addr vl        -> "valueAt" <+> pretty addr <> ":" <+> pretty vl
        CallSelectCoin walletID target -> "selectCoin" <+> pretty walletID <+> pretty target
        SelectCoinResult result        -> "selectCoin result:" <+> pretty result
        CallAllocateAddress            -> "allocateAddress"

wallets :: (Member (LogMsg MockWalletMsg) effs) => Eff effs [Wallet]
wallets = do
    logInfo CallWallets
    pure allWallets

fromWalletAPIError :: WalletAPIError -> ServerError
fromWalletAPIError (InsufficientFunds text) =
    err401 {errBody = BSL.fromStrict $ encodeUtf8 text}
fromWalletAPIError err@(PrivateKeyNotFound _) =
    err404 {errBody = BSL8.pack $ show err}
fromWalletAPIError (OtherError text) =
    err500 {errBody = BSL.fromStrict $ encodeUtf8 text}

valueAt ::
    ( Member (LogMsg MockWalletMsg) effs
    , Member ChainIndexEffect effs
    )
    => Address
    -> Eff effs Value
valueAt address = do
    logInfo CallValueAt
    value <- foldMap (txOutValue . txOutTxOut) . view (AddressMap.fundsAt address) <$> W.watchedAddresses
    logInfo $ ValueAtResponse address value
    pure value

selectCoin ::
    ( Member (LogMsg MockWalletMsg) effs
    , Member ChainIndexEffect effs
    , Member (Error ServerError) effs
    )
    => WalletId
    -> Value
    -> Eff effs ([(TxOutRef, Value)], Value)
selectCoin walletId target = do
    logInfo $ CallSelectCoin walletId target
    let address = EM.walletAddress (Wallet walletId)
    utxos :: UtxoMap <- view (AddressMap.fundsAt address) <$> W.watchedAddresses
    let funds :: [(TxOutRef, Value)]
        funds = fmap (second (txOutValue . txOutTxOut)) . Map.toList $ utxos
    result <- runM $ runError $ EM.selectCoin funds target
    logInfo $ SelectCoinResult result
    case result of
        Right value -> pure value
        Left err    -> throwError $ fromWalletAPIError err

allocateAddress ::
    ( LastMember m effs
    , Member (LogMsg MockWalletMsg) effs
    , MonadIO m
    )
    => WalletId
    -> Eff effs PubKey
allocateAddress _ = do
    logInfo CallAllocateAddress
    sendM $ liftIO $ generate arbitrary
