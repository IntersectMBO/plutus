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

import qualified Data.Aeson                                      as JSON
import           Data.UUID                                       (UUID)
import           GHC.Generics                                    (Generic)
import           Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription (..))
import           Plutus.PAB.Effects.Contract.ContractExe         (ContractExe)
import           Wallet.Types                                    (ContractInstanceId)

-- | Commands that can be interpreted with 'runCliCommand'
data Command
    = Migrate -- ^ Execute a database migration
    | MockNode -- ^ Run the mock node service
    | MockWallet -- ^ Run the mock wallet service
    | ChainIndex -- ^ Run the chain index service
    | Metadata -- ^ Run the mock meta-data service
    | ForkCommands [Command] -- ^ Fork  a list of commands
    | InstallContract ContractExe -- ^ Install a contract
    | ContractState ContractInstanceId -- ^ Display the contract identified by 'ContractInstanceId'
    | ReportContractHistory ContractInstanceId -- ^ Get the history of the contract identified by 'UUID'
    | ReportInstalledContracts -- ^ Get installed contracts
    | ReportActiveContracts -- ^ Get active contracts
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
