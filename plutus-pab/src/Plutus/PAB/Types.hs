{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}

module Plutus.PAB.Types where

import           Cardano.BM.Data.Tracer.Extras  (StructuredLog (..))
import qualified Cardano.ChainIndex.Types       as ChainIndex
import qualified Cardano.Metadata.Types         as Metadata
import qualified Cardano.Node.Server            as NodeServer
import qualified Cardano.SigningProcess.Server  as SigningProcess
import qualified Cardano.Wallet.Server          as WalletServer
import           Control.Lens.TH                (makePrisms)
import           Data.Aeson                     (FromJSON, ToJSON (..))
import qualified Data.HashMap.Strict            as HM
import           Data.Map.Strict                (Map)
import qualified Data.Map.Strict                as Map
import           Data.Text                      (Text)
import           Data.Text.Prettyprint.Doc      (Pretty, pretty, viaShow, (<+>))
import           Data.Time.Units                (Second)
import           Data.UUID                      (UUID)
import qualified Data.UUID.Extras               as UUID
import           GHC.Generics                   (Generic)
import           Language.Plutus.Contract.Trace (EndpointError (..))
import           Language.Plutus.Contract.Types (ContractError)
import           Ledger                         (Block, Blockchain, Tx, TxId, txId)
import           Ledger.Index                   as UtxoIndex
import           Plutus.PAB.Events              (ContractInstanceId)
import           Plutus.PAB.Instances           ()
import           Servant.Client                 (BaseUrl, ClientError)
import           Wallet.API                     (WalletAPIError)

newtype ContractExe =
    ContractExe
        { contractPath :: FilePath
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance StructuredLog ContractExe where
    toStructuredLog e = HM.singleton "contract" (toJSON e)

instance Pretty ContractExe where
    pretty ContractExe {contractPath} = "Path:" <+> pretty contractPath

data PABError
    = FileNotFound FilePath
    | ContractNotFound FilePath
    | ContractInstanceNotFound ContractInstanceId
    | PABContractError ContractError
    | WalletClientError ClientError
    | NodeClientError ClientError
    | MetadataError Metadata.MetadataError
    | SigningProcessError ClientError
    | ChainIndexError ClientError
    | WalletError WalletAPIError
    | ContractCommandError Int Text
    | InvalidUUIDError  Text
    | OtherError Text
    | EndpointCallError ContractInstanceId EndpointError
    deriving stock (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty PABError where
    pretty = \case
        FileNotFound fp            -> "File not found:" <+> pretty fp
        ContractNotFound fp        -> "Contract not found:" <+> pretty fp
        ContractInstanceNotFound i -> "Contract instance not found:" <+> pretty i
        PABContractError e         -> "Contract error:" <+> pretty e
        WalletClientError e        -> "Wallet client error:" <+> viaShow e
        NodeClientError e          -> "Node client error:" <+> viaShow e
        MetadataError e            -> "Metadata error:" <+> viaShow e
        SigningProcessError e      -> "Signing process error:" <+> viaShow e
        ChainIndexError e          -> "Chain index error:" <+> viaShow e
        WalletError e              -> "Wallet error:" <+> pretty e
        ContractCommandError i t   -> "Contract command error:" <+> pretty i <+> pretty t
        InvalidUUIDError t         -> "Invalid UUID:" <+> pretty t
        OtherError t               -> "Other error:" <+> pretty t
        EndpointCallError i e      -> "Endpoint call failed:" <+> pretty i <+> pretty e

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
        { dbConfig                :: DbConfig
        , walletServerConfig      :: WalletServer.Config
        , nodeServerConfig        :: NodeServer.MockServerConfig
        , metadataServerConfig    :: Metadata.MetadataConfig
        , pabWebserverConfig      :: WebserverConfig
        , chainIndexConfig        :: ChainIndex.ChainIndexConfig
        , signingProcessConfig    :: SigningProcess.SigningProcessConfig
        , requestProcessingConfig :: RequestProcessingConfig
        }
    deriving (Show, Eq, Generic, FromJSON)

newtype RequestProcessingConfig =
    RequestProcessingConfig
        { requestProcessingInterval :: Second -- ^ How many seconds to wait between calls to 'Plutus.PAB.Core.ContractInstance.processAllContractOutboxes'
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON)

data WebserverConfig =
    WebserverConfig
        { baseUrl   :: BaseUrl
        , staticDir :: FilePath
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

data Source
    = ContractEventSource
    | WalletEventSource
    | UserEventSource
    | NodeEventSource
    deriving (Show, Eq)

toUUID :: Source -> UUID
toUUID source =
    UUID.sequenceIdToMockUUID $
    case source of
        ContractEventSource -> 1
        WalletEventSource   -> 2
        UserEventSource     -> 3
        NodeEventSource     -> 4

data ChainOverview =
    ChainOverview
        { chainOverviewBlockchain     :: Blockchain
        , chainOverviewUnspentTxsById :: Map TxId Tx
        , chainOverviewUtxoIndex      :: UtxoIndex
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

mkChainOverview :: Blockchain -> ChainOverview
mkChainOverview = foldl reducer emptyChainOverview
  where
    reducer :: ChainOverview -> Block -> ChainOverview
    reducer ChainOverview { chainOverviewBlockchain = oldBlockchain
                          , chainOverviewUnspentTxsById = oldTxById
                          , chainOverviewUtxoIndex = oldUtxoIndex
                          } txs =
        let unprunedTxById =
                foldl (\m tx -> Map.insert (txId tx) tx m) oldTxById txs
            newTxById = id unprunedTxById -- TODO Prune spent keys.
            newUtxoIndex = UtxoIndex.insertBlock txs oldUtxoIndex
         in ChainOverview
                { chainOverviewBlockchain = txs : oldBlockchain
                , chainOverviewUnspentTxsById = newTxById
                , chainOverviewUtxoIndex = newUtxoIndex
                }
    emptyChainOverview =
        ChainOverview
            { chainOverviewBlockchain = []
            , chainOverviewUnspentTxsById = Map.empty
            , chainOverviewUtxoIndex = UtxoIndex Map.empty
            }

makePrisms ''PABError
