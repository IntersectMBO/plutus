{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}

module Plutus.SCB.Types where

import           Data.Aeson                         (FromJSON, ToJSON)
import qualified Data.Aeson                         as Aeson
import           Data.Text                          (Text)
import           Data.UUID                          (UUID)
import           GHC.Generics                       (Generic)
import           Language.Plutus.Contract.Resumable (ResumableError)

newtype Contract =
    Contract
        { contractPath :: FilePath
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON)

data ActiveContract =
    ActiveContract
        { activeContractId   :: UUID
        , activeContractPath :: FilePath
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON)

data SCBError
    = FileNotFound FilePath
    | ContractNotFound FilePath
    | ContractError (ResumableError Text)
    deriving (Show, Eq)

data PartiallyDecodedResponse =
    PartiallyDecodedResponse
        { newState :: Aeson.Value
        , hooks    :: Aeson.Value
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

data DbConfig =
    DbConfig
        { dbConfigFile     :: Text
        -- ^ The path to the sqlite database file. May be absolute or relative.
        , dbConfigPoolSize :: Int
        -- ^ Max number of concurrent sqlite database connections.
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)
