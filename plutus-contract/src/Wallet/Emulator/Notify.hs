{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeOperators      #-}
-- | Implements contract instance notifications in the emulator.
module Wallet.Emulator.Notify(
    EmulatorContractNotifyEffect(..)
    , sendAgentNotification
    , handleContractRuntime
    -- * Contract instance IDs
    , walletInstanceId
    , instanceIdWallet
    -- * Logging
    , EmulatorNotifyLogMsg(..)
    ) where

import           Control.Monad.Freer
import           Control.Monad.Freer.Log   (LogMsg, logWarn)
import           Control.Monad.Freer.TH    (makeEffect)
import           Data.Aeson                (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc
import qualified Data.UUID.Extras          as UUID
import           GHC.Generics              (Generic)


import           Wallet.Effects            (ContractRuntimeEffect (..))
import           Wallet.Emulator.Wallet    (Wallet (..))
import           Wallet.Types              (ContractInstanceId (..), Notification (..), NotificationError (..))

data EmulatorContractNotifyEffect r where
    SendAgentNotification :: Wallet -> Wallet -> Notification -> EmulatorContractNotifyEffect (Maybe NotificationError)

makeEffect ''EmulatorContractNotifyEffect

{- Note [Emulator contract instances]

In the emulator, unlike the PAB, there is no distinction between agents (called
wallets) and instances. Every emulated agent runs one instance of
the same contract. We don't have any 'ContractInstanceId' values in
the emulator either. The 'Notify' effect however uses contract instance IDs to
identify the recipients of notifications.

Therefore we need a mapping between agents/wallets and contract instance IDs.
This mapping is given by the 'walletInstanceId' and 'instanceIdWallet'
functions below.

-}

-- | The 'ContractInstanceId' of a wallet.
--   See note [Emulator contract instances].
walletInstanceId :: Wallet -> ContractInstanceId
walletInstanceId (Wallet i) =
    ContractInstanceId . UUID.sequenceIdToMockUUID $ fromIntegral i

-- | The wallet of a 'ContractInstanceId'.
--   See note [Emulator contract instances].
instanceIdWallet :: ContractInstanceId -> Maybe Wallet
instanceIdWallet (ContractInstanceId u) =
    Wallet . fromIntegral <$> UUID.mockUUIDToSequenceId u

-- | Handle the 'ContractRuntimeEffect' by forwarding notifications to
--   'EmulatorContractNotifyEffect'
handleContractRuntime ::
    ( Member (LogMsg EmulatorNotifyLogMsg) effs
    , Member EmulatorContractNotifyEffect effs
    )
    => Wallet
    -> ContractRuntimeEffect
    ~> Eff effs
handleContractRuntime source = \case
    SendNotification n -> do
        let Notification{notificationContractID} = n
        case instanceIdWallet notificationContractID of
            Nothing -> do
                let err = InstanceDoesNotExist notificationContractID
                logWarn $ NotifyFailed source err
                pure $ Just err
            Just recipient -> sendAgentNotification source recipient n

---
-- Logging
---

data EmulatorNotifyLogMsg =
    NotifyFailed Wallet NotificationError
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty EmulatorNotifyLogMsg where
    pretty = \case
        NotifyFailed w n -> pretty w <> colon <+> pretty n
