{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE TypeApplications #-}

module Cardano.Wallet.Client where

import           Cardano.Wallet.API     (API)
import           Cardano.Wallet.Types   (WalletId)
import           Control.Lens
import           Data.Function          ((&))
import           Data.Proxy             (Proxy (Proxy))
import           Ledger                 (Address, PubKey, TxOutRef, Value, pubKeyAddress)
import           Ledger.AddressMap      (AddressMap, UtxoMap, fundsAt)
import           Servant                (NoContent)
import           Servant.Client         (ClientM, client)
import           Servant.Extra          (left, right)
import           Wallet.Emulator.Wallet (Wallet)

selectCoins :: WalletId -> Value -> ClientM ([(TxOutRef, Value)], Value)
allocateAddress :: WalletId -> ClientM PubKey
getWatchedAddresses :: ClientM AddressMap
getWallets :: ClientM [Wallet]
getOwnPubKey :: ClientM PubKey
startWatching :: Address -> ClientM NoContent
valueAt :: Address -> ClientM Value
(getWallets, getOwnPubKey, getWatchedAddresses, startWatching, selectCoins, allocateAddress, valueAt) =
    ( getWallets_
    , getOwnPubKey_
    , getWatchedAddresses_
    , startWatching_
    , selectCoins_
    , allocateAddress_
    , valueAt_)
  where
    api = client (Proxy @API)
    getWallets_ = api & left
    getOwnPubKey_ = api & right & left
    getWatchedAddresses_ = api & right & right & left
    startWatching_ = api & right & right & right & left
    byWalletId = api & right & right & right & right & left
    selectCoins_ walletId = byWalletId walletId & left
    allocateAddress_ walletId = byWalletId walletId & right
    valueAt_ = api & right & right & right & right & right

getOwnOutputs :: ClientM UtxoMap
getOwnOutputs = do
    pk <- getOwnPubKey
    am <- getWatchedAddresses
    pure $ am ^. fundsAt (pubKeyAddress pk)
