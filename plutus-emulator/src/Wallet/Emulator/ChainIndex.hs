{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
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
import           Data.Function              ((&))
import           Data.Text.Prettyprint.Doc
import           GHC.Generics               (Generic)
import qualified Wallet.API                 as WAPI
import           Wallet.Emulator.NodeClient (Notification (..))

import           Ledger.Address             (Address)
import           Ledger.AddressMap          (AddressMap)
import qualified Ledger.AddressMap          as AM

data ChainIndexEffect r where
    StartWatching :: Address -> ChainIndexEffect ()
    WatchedAddresses :: ChainIndexEffect AM.AddressMap
    ChainIndexNotify :: Notification -> ChainIndexEffect ()
makeEffect ''ChainIndexEffect

data ChainIndexEvent =
    AddressStartWatching Address
    | ReceiveBlockNotification
    deriving stock (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty ChainIndexEvent where
    pretty (AddressStartWatching addr) = "StartWatching:" <+> pretty addr
    pretty ReceiveBlockNotification    = "ReceiveBlockNotification"

newtype ChainIndexState =
    ChainIndexState
        { _idxWatchedAddresses :: AddressMap
        }
        deriving stock (Eq, Show)
        deriving newtype (Semigroup, Monoid)
makeLenses ''ChainIndexState

type ChainIndexEffs = '[State ChainIndexState, Writer [ChainIndexEvent]]

instance (Member ChainIndexEffect effs) => WAPI.ChainIndexAPI (Eff effs) where
    watchedAddresses = watchedAddresses
    startWatching = startWatching

handleChainIndex
    :: (Members ChainIndexEffs effs)
    => Eff (ChainIndexEffect ': effs) ~> Eff effs
handleChainIndex = interpret $ \case
    ChainIndexNotify notification -> case notification of
        BlockValidated txns -> tell [ReceiveBlockNotification] >> (modify $ \s ->
            s & idxWatchedAddresses %~ (\am -> foldl (\am' t -> AM.updateAllAddresses t am') am txns))
        _ -> pure ()
    StartWatching addr -> tell [AddressStartWatching addr] >> (modify $ \s ->
        s & idxWatchedAddresses %~ AM.addAddress addr)
    WatchedAddresses -> gets _idxWatchedAddresses
