{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE TypeApplications #-}

module Cardano.Wallet.Client where

import           Cardano.Wallet.API     (API)
import           Cardano.Wallet.Types   (WalletId)
import           Control.Lens
import           Data.Function          ((&))
import           Data.Proxy             (Proxy (Proxy))
import           Ledger                 (Address, PubKey, Value, pubKeyAddress)
import           Ledger.AddressMap      (AddressMap, UtxoMap, fundsAt)
import           Servant                (NoContent)
import           Servant.Client         (ClientM, client)
import           Servant.Extra          (left, right)
import           Wallet.Emulator.Wallet (Wallet)

selectCoins :: WalletId -> Value -> ClientM ([Value], Value)
allocateAddress :: WalletId -> ClientM PubKey
getWatchedAddresses :: ClientM AddressMap
getWallets :: ClientM [Wallet]
getOwnPubKey :: ClientM PubKey
startWatching :: Address -> ClientM NoContent
(getWallets, getOwnPubKey, getWatchedAddresses, startWatching, selectCoins, allocateAddress) =
    ( getWallets_
    , getOwnPubKey_
    , getWatchedAddresses_
    , startWatching_
    , selectCoins_
    , allocateAddress_)
  where
    api = client (Proxy @API)
    getWallets_ = api & left
    active_ = api & right & left
    getOwnPubKey_ = active_ & left
    getWatchedAddresses_ = active_ & right & left
    startWatching_ = active_ & right & right
    byWalletId = api & right & right
    selectCoins_ walletId = byWalletId walletId & left
    allocateAddress_ walletId = byWalletId walletId & right

getOwnOutputs :: ClientM UtxoMap
getOwnOutputs = do
  pk <- getOwnPubKey
  am <- getWatchedAddresses
  pure $ am ^. fundsAt (pubKeyAddress pk)
