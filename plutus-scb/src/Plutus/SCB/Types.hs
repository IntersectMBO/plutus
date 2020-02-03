{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}

module Plutus.SCB.Types where

import           Data.Aeson                         (FromJSON, ToJSON)
import qualified Data.Aeson                         as Aeson
import qualified Data.Aeson.Encode.Pretty           as JSON
import qualified Data.ByteString.Lazy.Char8         as BS8
import           Data.Text                          (Text)
import           Data.UUID                          (UUID)
import           GHC.Generics                       (Generic)
import           Language.Plutus.Contract.Resumable (ResumableError)
import           Options.Applicative.Help.Pretty    (Pretty, indent, pretty, string, text, vsep, (<+>))

newtype Contract =
    Contract
        { contractPath :: FilePath
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty Contract where
    pretty Contract {contractPath} = "Path:" <+> text contractPath

data ActiveContract =
    ActiveContract
        { activeContractId   :: UUID
        , activeContractPath :: FilePath
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty ActiveContract where
    pretty ActiveContract {activeContractId, activeContractPath} =
        vsep
            [ "UUID:" <+> text (show activeContractId)
            , "Path:" <+> text activeContractPath
            ]

data SCBError
    = FileNotFound FilePath
    | ContractNotFound FilePath
    | ContractError (ResumableError Text)
    | ContractCommandError Int Text
    deriving (Show, Eq)

data PartiallyDecodedResponse =
    PartiallyDecodedResponse
        { newState :: Aeson.Value
        , hooks    :: Aeson.Value
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty PartiallyDecodedResponse where
    pretty PartiallyDecodedResponse {newState, hooks} =
        vsep
            [ "State:"
            , indent 2 $ string $ BS8.unpack $ JSON.encodePretty newState
            , "Hooks:"
            , indent 2 $ string $ BS8.unpack $ JSON.encodePretty hooks
            ]

data ActiveContractState =
    ActiveContractState
        { activeContract           :: ActiveContract
        , partiallyDecodedResponse :: PartiallyDecodedResponse
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty ActiveContractState where
    pretty ActiveContractState {activeContract, partiallyDecodedResponse} =
        vsep
            [ "Contract:"
            , indent 2 $ pretty activeContract
            , "Status:"
            , indent 2 $ pretty partiallyDecodedResponse
            ]

data DbConfig =
    DbConfig
        { dbConfigFile     :: Text
        -- ^ The path to the sqlite database file. May be absolute or relative.
        , dbConfigPoolSize :: Int
        -- ^ Max number of concurrent sqlite database connections.
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)
