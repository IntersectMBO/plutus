{-# LANGUAGE ApplicativeDo         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Command (Command (..)) where

import qualified Data.Aeson                             as JSON
import           Data.UUID                              (UUID)
import           GHC.Generics                           (Generic)
import           Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription (..))

-- | Commands that can be interpreted with 'runCliCommand'
data Command
    = Migrate -- ^ Execute a database migration
    | MockNode -- ^ Run the mock node service
    | MockWallet -- ^ Run the mock wallet service
    | ChainIndex -- ^ Run the chain index service
    | Metadata -- ^ Run the mock meta-data service
    | ForkCommands [Command] -- ^ Fork  a list of commands
    | InstallContract FilePath -- ^ Install a contract
    | ActivateContract FilePath -- ^ Activate a contract
    | ContractState UUID -- ^ Display the contract identified by 'UUID'
    | UpdateContract UUID EndpointDescription JSON.Value -- ^ Update the contract details of the contract identified by 'UUID'
    | ReportContractHistory UUID -- ^ Get the history of the contract identified by 'UUID'
    | ReportInstalledContracts -- ^ Get installed contracts
    | ReportActiveContracts -- ^ Get active contracts
    | ProcessContractInbox UUID -- ^ Run the contract-inbox service
    | ProcessAllContractOutboxes -- ^ DEPRECATED
    | ReportTxHistory -- ^ List transaction history
    | PABWebserver -- ^ Run the PAB webserver
    | PSGenerator -- ^ Generate purescript bridge code
          { _outputDir :: !FilePath -- ^ Path to write generated code to
          }
    | WriteDefaultConfig -- ^ Write default logging configuration
          { _outputFile :: !FilePath -- ^ Path to write configuration to
          }
    | StartSimulatorWebServer -- ^ Start a simulator with some predefined contracts, no interaction with external services
    deriving stock (Show, Eq, Generic)
    deriving anyclass JSON.ToJSON
