
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS -Wno-orphans #-} -- TODO: remove this
module Cardano.Protocol.Socket.Type where

import           Codec.Serialise.Class                              (Serialise)
import           Data.Aeson                                         (FromJSON, ToJSON)
import qualified Data.ByteString.Lazy                               as BSL
import           Data.Text.Prettyprint.Doc                          (Pretty)

import           Cardano.Prelude                                    (NoUnexpectedThunks)
import           GHC.Generics
import           Network.Socket                                     as Socket

import           Codec.Serialise                                    (DeserialiseFailure)
import qualified Codec.Serialise                                    as CBOR
import           Network.TypedProtocol.Codec
import           Ouroboros.Network.Block                            (HeaderHash, StandardHash)
import           Ouroboros.Network.Mux
import qualified Ouroboros.Network.Protocol.ChainSync.Codec         as ChainSync
import qualified Ouroboros.Network.Protocol.ChainSync.Type          as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Codec as TxSubmission
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Type  as TxSubmission

-- import           Cardano.Protocol.Node
import           Ledger                                             (Block, Tx (..), TxId (..), txId)
import qualified Ledger.Index                                       as Index
import           LedgerBytes                                        (LedgerBytes (..))
import           Wallet.Emulator.Chain

-- CBOR Serialisation
deriving newtype instance CBOR.Serialise Index.UtxoIndex
deriving instance Generic ChainState
deriving instance Serialise ChainState

type Tip = Block

-- Block header
newtype BlockId = BlockId { getBlockId :: BSL.ByteString }
  deriving (Eq, Ord, Generic)
  deriving anyclass (ToJSON, FromJSON)
  deriving newtype (Serialise, NoUnexpectedThunks)
  deriving (Pretty, Show) via LedgerBytes

blockId :: Block -> BlockId
blockId = BlockId . foldl BSL.append BSL.empty . map (getTxId . txId)

-- Making Tx work with the node protocols
type instance HeaderHash Tx = TxId
type instance HeaderHash Block = BlockId
deriving instance StandardHash Tx

deriving instance StandardHash Block
deriving newtype instance NoUnexpectedThunks TxId


maximumMiniProtocolLimits :: MiniProtocolLimits
maximumMiniProtocolLimits =
    MiniProtocolLimits {
        maximumIngressQueue = maxBound
    }

nodeApplication
  :: RunMiniProtocol appType bytes m a b
  -> RunMiniProtocol appType bytes m a b
  -> OuroborosApplication appType bytes m a b
nodeApplication chainSync txSubmission =
    OuroborosApplication [
      MiniProtocol {
        miniProtocolNum = MiniProtocolNum 2,
        miniProtocolLimits = maximumMiniProtocolLimits,
        miniProtocolRun = chainSync
      },
      MiniProtocol {
        miniProtocolNum = MiniProtocolNum 3,
        miniProtocolLimits = maximumMiniProtocolLimits,
        miniProtocolRun = txSubmission
      }
    ]

type Offset = Int

-- Codec specialisations for the mock node protocol
codecChainSync :: Codec (ChainSync.ChainSync Block Block)
                        DeserialiseFailure
                        IO BSL.ByteString
codecChainSync =
    ChainSync.codecChainSync
      CBOR.encode             CBOR.decode
      CBOR.encode             CBOR.decode
      CBOR.encode             CBOR.decode

codecTxSubmission :: Codec (TxSubmission.LocalTxSubmission Tx String)
                           DeserialiseFailure
                           IO BSL.ByteString
codecTxSubmission =
    TxSubmission.codecLocalTxSubmission
      CBOR.encode CBOR.decode
      CBOR.encode CBOR.decode

mkLocalSocketAddrInfo :: FilePath -> Socket.AddrInfo
mkLocalSocketAddrInfo path =
    Socket.AddrInfo
      []
      Socket.AF_UNIX
      Socket.Stream
      Socket.defaultProtocol
      (Socket.SockAddrUnix path)
      Nothing
