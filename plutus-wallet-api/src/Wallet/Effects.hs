{-# LANGUAGE GADTs           #-}
{-# LANGUAGE TemplateHaskell #-}
module Wallet.Effects where

import           Control.Monad.Freer.TH
import qualified Data.Set               as Set
import           Data.Text              (Text)
import           Ledger                 (Address, PubKey, PubKeyHash, Slot, Tx, TxIn, TxOut, Value)
import           Ledger.AddressMap      (AddressMap, UtxoMap)

data WalletEffect r where
    SubmitTxn :: Tx -> WalletEffect ()
    OwnPubKey :: WalletEffect PubKey
    UpdatePaymentWithChange :: Value -> (Set.Set TxIn, Maybe TxOut) -> WalletEffect (Set.Set TxIn, Maybe TxOut)
    WalletSlot :: WalletEffect Slot
    WalletLogMsg :: Text -> WalletEffect ()
    OwnOutputs :: WalletEffect UtxoMap
makeEffect ''WalletEffect

data NodeClientEffect r where
    PublishTx :: Tx -> NodeClientEffect ()
    GetClientSlot :: NodeClientEffect Slot
    GetClientIndex :: NodeClientEffect AddressMap
makeEffect ''NodeClientEffect

data SigningProcessEffect r where
    AddSignatures :: [PubKeyHash] -> Tx -> SigningProcessEffect Tx
makeEffect ''SigningProcessEffect

data ChainIndexEffect r where
    StartWatching :: Address -> ChainIndexEffect ()
    WatchedAddresses :: ChainIndexEffect AddressMap
makeEffect ''ChainIndexEffect
