{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Plutus.PAB.Core
    ( dbConnect
    , installContract
    , activateContractSTM
    , reportContractState
    , Connection(Connection)
    , toUUID
    -- * Effects
    , CoreMsg(..)
    ) where

import           Cardano.BM.Data.Tracer                  (ToObject (..), TracingVerbosity (..))
import           Cardano.BM.Data.Tracer.Extras           (StructuredLog, mkObjectStr)
import           Control.Monad.Freer                     (Eff, Member)
import           Control.Monad.Freer.Extras.Log          (LogMsg, logInfo)
import           Control.Monad.IO.Unlift                 (MonadUnliftIO)
import           Control.Monad.Logger                    (MonadLogger)
import qualified Control.Monad.Logger                    as MonadLogger
import           Data.Aeson                              (FromJSON, ToJSON (..))
import           Data.Text.Prettyprint.Doc               (Pretty, pretty, (<+>))
import           Database.Persist.Sqlite                 (createSqlitePoolFromInfo, mkSqliteConnectionInfo)
import           Eventful.Store.Sql                      (defaultSqlEventStoreConfig)
import           GHC.Generics                            (Generic)
import           Plutus.PAB.Core.ContractInstance        (activateContractSTM)
import           Plutus.PAB.Effects.Contract             (ContractDefinitionStore, ContractStore, PABContract (..),
                                                          addDefinition, getState)
import           Plutus.PAB.Effects.EventLog             (Connection (..))
import qualified Plutus.PAB.Effects.EventLog             as EventLog
import           Plutus.PAB.Events.Contract              (ContractPABRequest)
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import           Plutus.PAB.Types                        (DbConfig (DbConfig), dbConfigFile, dbConfigPoolSize, toUUID)
import           Wallet.Types                            (ContractInstanceId)

data CoreMsg t =
    Installing t
    | Installed
    | FindingContract ContractInstanceId
    | FoundContract (Maybe (PartiallyDecodedResponse ContractPABRequest))
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty t => Pretty (CoreMsg t) where
    pretty = \case
        Installing d      -> "Installing" <+> pretty d
        Installed         -> "Installed"
        FindingContract i -> "Finding contract" <+> pretty i
        FoundContract c   -> "Found contract" <+> pretty c

instance (StructuredLog t, ToJSON t) => ToObject (CoreMsg t) where
    toObject v = \case
        Installing t ->
            mkObjectStr "installing contract" t
        Installed ->
            mkObjectStr "contract installed" ()
        FindingContract instanceID ->
            mkObjectStr "finding contract instance" instanceID
        FoundContract state ->
            mkObjectStr "found contract" $
                case v of
                    MaximalVerbosity -> Left state
                    _                -> Right ()

installContract ::
    forall t effs.
    ( Member (LogMsg (CoreMsg (ContractDef t))) effs
    , Member (ContractDefinitionStore t) effs
    )
    => (ContractDef t)
    -> Eff effs ()
installContract contractHandle = do
    logInfo @(CoreMsg (ContractDef t)) $ Installing contractHandle
    addDefinition @t contractHandle
    logInfo @(CoreMsg (ContractDef t)) Installed

reportContractState ::
    forall t effs.
    ( Member (LogMsg (CoreMsg t)) effs
    , Member (ContractStore t) effs
    , State t ~ PartiallyDecodedResponse ContractPABRequest
    )
    => ContractInstanceId
    -> Eff effs ()
reportContractState cid = do
    logInfo @(CoreMsg t) $ FindingContract cid
    contractState <- getState @t cid
    logInfo @(CoreMsg t) $ FoundContract $ Just contractState

------------------------------------------------------------
-- | Create a database 'Connection' containing the connection pool
-- plus some configuration information.
dbConnect ::
    ( MonadUnliftIO m
    , MonadLogger m
    )
    => DbConfig
    -> m EventLog.Connection
dbConnect DbConfig {dbConfigFile, dbConfigPoolSize} = do
    let connectionInfo = mkSqliteConnectionInfo dbConfigFile
    MonadLogger.logDebugN "Connecting to DB"
    connectionPool <- createSqlitePoolFromInfo connectionInfo dbConfigPoolSize
    pure $ EventLog.Connection (defaultSqlEventStoreConfig, connectionPool)
