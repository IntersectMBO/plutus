{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}

module Plutus.SCB.Types where

import qualified Cardano.ChainIndex.Types                   as ChainIndex
import qualified Cardano.Node.Server                        as NodeServer
import qualified Cardano.SigningProcess.Server              as SigningProcess
import qualified Cardano.Wallet.Server                      as WalletServer
import           Control.Lens.TH                            (makePrisms)
import           Data.Aeson                                 (FromJSON, ToJSON)
import qualified Data.Aeson                                 as Aeson
import qualified Data.Aeson.Encode.Pretty                   as JSON
import qualified Data.ByteString.Lazy.Char8                 as BS8
import           Data.Text                                  (Text)
import           Data.Text.Prettyprint.Doc                  (Pretty, indent, pretty, vsep, (<+>))
import           Data.UUID                                  (UUID)
import qualified Data.UUID                                  as UUID
import           GHC.Generics                               (Generic)
import           Language.Plutus.Contract.Effects.OwnPubKey (OwnPubKeyRequest)
import           Language.Plutus.Contract.Resumable         (ResumableError)
import           Ledger.Address                             (Address)
import           Ledger.Constraints                         (UnbalancedTx)
import           Servant.Client                             (ServantError)
import           Wallet.API                                 (WalletAPIError)

newtype Contract =
    Contract
        { contractPath :: FilePath
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty Contract where
    pretty Contract {contractPath} = "Path:" <+> pretty contractPath

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
            [ "UUID:" <+> pretty (show activeContractId)
            , "Path:" <+> pretty activeContractPath
            ]

data SCBError
    = FileNotFound FilePath
    | ContractNotFound FilePath
    | ActiveContractStateNotFound UUID
    | ContractError (ResumableError Text)
    | WalletClientError ServantError
    | NodeClientError ServantError
    | SigningProcessError ServantError
    | WalletError WalletAPIError
    | ContractCommandError Int Text
    | OtherError Text
    deriving (Show, Eq)

data ContractHook
    = UtxoAtHook Address
    | TxHook UnbalancedTx
    | OwnPubKeyHook OwnPubKeyRequest
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
            , indent 2 $ pretty $ BS8.unpack $ JSON.encodePretty newState
            , "Hooks:"
            , indent 2 $ pretty $ BS8.unpack $ JSON.encodePretty hooks
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

data Config =
    Config
        { dbConfig             :: DbConfig
        , walletServerConfig   :: WalletServer.Config
        , nodeServerConfig     :: NodeServer.MockServerConfig
        , chainIndexConfig     :: ChainIndex.ChainIndexConfig
        , signingProcessConfig :: SigningProcess.SigningProcessConfig
        }
    deriving (Show, Eq, Generic, FromJSON)

data Source
    = ContractEventSource
    | WalletEventSource
    | UserEventSource
    | NodeEventSource
    deriving (Show, Eq)

toUUID :: Source -> UUID
toUUID ContractEventSource = UUID.fromWords 0 0 0 1
toUUID WalletEventSource   = UUID.fromWords 0 0 0 2
toUUID UserEventSource     = UUID.fromWords 0 0 0 3
toUUID NodeEventSource     = UUID.fromWords 0 0 0 4

makePrisms ''SCBError
