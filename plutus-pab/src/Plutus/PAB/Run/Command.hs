{-# LANGUAGE ApplicativeDo         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Plutus.PAB.Run.Command
    ( ConfigCommand(..)
    , NoConfigCommand(..)
    , allServices
    ) where

import qualified Data.Aeson   as JSON
import           GHC.Generics (Generic)
import           Wallet.Types (ContractInstanceId)

-- | A command for which a config.yaml file is required
data ConfigCommand =
    Migrate
    | StartMockNode -- ^ Run the mock node service
    | MockWallet -- ^ Run the mock wallet service
    | ChainIndex -- ^ Run the chain index service
    | ForkCommands [ConfigCommand] -- ^ Fork a list of commands
    | ContractState ContractInstanceId -- ^ Display the contract identified by 'ContractInstanceId'
    | ReportContractHistory ContractInstanceId -- ^ Get the history of the contract identified by 'UUID'
    | ReportAvailableContracts -- ^ Get all available contracts
    | ReportActiveContracts -- ^ Get active contracts
    | PABWebserver -- ^ Run the PAB webserver
    | PSApiGenerator -- ^ Generate purescript bridge code
          { psApiGenOutputDir :: !FilePath -- ^ Path to write generated code to
          }
    deriving stock (Show, Eq, Generic)
    deriving anyclass JSON.ToJSON


-- | A single command to the PAB that spins up all the necessary services.
allServices :: ConfigCommand
allServices =
  ForkCommands
    [ StartMockNode
    , ChainIndex
    , MockWallet
    , PABWebserver
    ]


data NoConfigCommand =
    PSGenerator -- ^ Generate purescript bridge code
          { psGenOutputDir :: !FilePath -- ^ Path to write generated code to
          }
    | WriteDefaultConfig -- ^ Write default logging configuration
          { outputFile :: !FilePath -- ^ Path to write configuration to
          }
    deriving stock (Show, Eq, Generic)
    deriving anyclass JSON.ToJSON
