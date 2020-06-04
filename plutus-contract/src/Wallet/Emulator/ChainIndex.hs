{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans  #-}
module Wallet.Emulator.ChainIndex where

import           Control.Lens
import           Control.Monad.Freer
import           Control.Monad.Freer.State
import           Control.Monad.Freer.TH
import           Control.Monad.Freer.Writer
import           Data.Aeson                 (FromJSON, ToJSON)
import           Data.Semigroup.Generic     (GenericSemigroupMonoid (..))
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Data.Text.Prettyprint.Doc
import           GHC.Generics               (Generic)
import           Wallet.Effects             (ChainIndexEffect (..))
import           Wallet.Emulator.NodeClient (BlockValidated (..))

import           Ledger.Address             (Address)
import           Ledger.AddressMap          (AddressMap)
import qualified Ledger.AddressMap          as AM
import           Ledger.Tx                  (txId)
import           Ledger.TxId                (TxId)

data ChainIndexControlEffect r where
    ChainIndexNotify :: BlockValidated -> ChainIndexControlEffect ()
makeEffect ''ChainIndexControlEffect

data ChainIndexEvent =
    AddressStartWatching Address
    | ReceiveBlockNotification
    deriving stock (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty ChainIndexEvent where
    pretty (AddressStartWatching addr) = "StartWatching:" <+> pretty addr
    pretty ReceiveBlockNotification    = "ReceiveBlockNotification"

data ChainIndexState =
    ChainIndexState
        { _idxWatchedAddresses      :: AddressMap
        , _idxConfirmedTransactions :: Set TxId
        }
        deriving stock (Eq, Show, Generic)
        deriving (Semigroup, Monoid) via (GenericSemigroupMonoid ChainIndexState)

makeLenses ''ChainIndexState

type ChainIndexEffs = '[State ChainIndexState, Writer [ChainIndexEvent]]

handleChainIndexControl
    :: (Members ChainIndexEffs effs)
    => Eff (ChainIndexControlEffect ': effs) ~> Eff effs
handleChainIndexControl = interpret $ \case
    ChainIndexNotify (BlockValidated txns) ->
        tell [ReceiveBlockNotification] >> (modify $ \s ->
            s & idxWatchedAddresses %~ (\am -> foldl (\am' t -> AM.updateAllAddresses t am') am txns)
            & idxConfirmedTransactions <>~ foldMap (Set.singleton . txId) txns
            )

handleChainIndex
    :: (Members ChainIndexEffs effs)
    => Eff (ChainIndexEffect ': effs) ~> Eff effs
handleChainIndex = interpret $ \case
    StartWatching addr -> tell [AddressStartWatching addr] >> (modify $ \s ->
        s & idxWatchedAddresses %~ AM.addAddress addr)
    WatchedAddresses -> gets _idxWatchedAddresses
    TransactionConfirmed txid -> Set.member txid <$> gets _idxConfirmedTransactions
