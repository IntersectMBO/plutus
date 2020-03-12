{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS -Wno-orphans #-} -- TODO: remove this
module Cardano.Protocol.Type where

import           Codec.Serialise.Class                              (Serialise)
import           Data.Aeson                                         (FromJSON, ToJSON)
import qualified Data.ByteString.Lazy                               as BSL
import           Data.Text.Prettyprint.Doc                          (Pretty)

import           Control.Concurrent.STM
import           Control.Lens                                       hiding (index)
import           GHC.Generics
import           Network.Socket                                     as Socket

import           Cardano.Prelude                                    (NoUnexpectedThunks)
import           Cardano.Slotting.Slot                              (SlotNo (..))
import           Ouroboros.Network.Block                            (HeaderHash, StandardHash)
import           Ouroboros.Network.Mux

import qualified Cardano.Protocol.Puppet.Codec                      as Puppet
import qualified Cardano.Protocol.Puppet.Type                       as Puppet
import           Codec.Serialise                                    (DeserialiseFailure)
import qualified Codec.Serialise                                    as CBOR
import           Network.TypedProtocol.Codec
import qualified Ouroboros.Network.Protocol.ChainSync.Codec         as ChainSync
import qualified Ouroboros.Network.Protocol.ChainSync.Type          as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Codec as TxSubmission
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Type  as TxSubmission

import           Ledger                                             (Block, Slot (..), Tx (..), TxId (..), txId)
import qualified Ledger.Index                                       as Index
import           LedgerBytes                                        (LedgerBytes (..))
import           Wallet.Emulator.Chain

-- Making plutus transaction representations work with the node protocols
type instance HeaderHash Tx = TxId
type instance HeaderHash Block = BlockId
deriving instance StandardHash Tx
deriving instance StandardHash Block

deriving instance Generic Index.UtxoIndex
deriving newtype instance CBOR.Serialise Index.UtxoIndex
deriving newtype instance NoUnexpectedThunks TxId
deriving instance Generic ChainState
deriving instance Serialise ChainState
-- TODO: Move this when fear of merging subsides

-- Block header
newtype BlockId = BlockId { getBlockId :: BSL.ByteString }
  deriving (Eq, Ord, Generic)
  deriving anyclass (ToJSON, FromJSON)
  deriving newtype (Serialise, NoUnexpectedThunks)
  deriving (Pretty, Show) via LedgerBytes

blockId :: Block -> BlockId
blockId = BlockId . foldl BSL.append BSL.empty . map (getTxId . txId)
--

type Tip = Block

data NodeToClientPtcls = ChainSyncWithBlocksPtcl
                       | LocalTxSubmissionPtcl
                       | PuppetPtcl
      deriving (Eq, Ord, Enum, Bounded, Show)

instance MiniProtocolLimits NodeToClientPtcls where
    maximumMessageSize _  = maxBound
    maximumIngressQueue _ = maxBound

instance ProtocolEnum NodeToClientPtcls where
    fromProtocolEnum ChainSyncWithBlocksPtcl = MiniProtocolNum 2
    fromProtocolEnum LocalTxSubmissionPtcl   = MiniProtocolNum 3
    fromProtocolEnum PuppetPtcl              = MiniProtocolNum 4

type Offset = Int

data PuppetHandle =
     PuppetHandle {
       txInputQueue :: TQueue Tx
     , ctlRequest   :: TQueue PuppetRequest
     , ctlResponse  :: TQueue PuppetResponse
     }

data PuppetRequest = RequestState
                   | RequestValidation

data PuppetResponse = ResponseState ChainState
                    | Validated Block

newPuppetHandle :: IO PuppetHandle
newPuppetHandle =
  atomically $ PuppetHandle <$> newTQueue <*> newTQueue <*> newTQueue

-- Codec specialisations for the mock node protocol
codecChainSync :: Codec (ChainSync.ChainSync Block Block)
                        DeserialiseFailure
                        IO BSL.ByteString
codecChainSync =
    ChainSync.codecChainSync
      CBOR.encode (fmap const CBOR.decode)
      CBOR.encode             CBOR.decode
      CBOR.encode             CBOR.decode

codecTxSubmission :: Codec (TxSubmission.LocalTxSubmission Tx String)
                           DeserialiseFailure
                           IO BSL.ByteString
codecTxSubmission =
    TxSubmission.codecLocalTxSubmission
      CBOR.encode CBOR.decode
      CBOR.encode CBOR.decode

codecPuppet :: Codec (Puppet.Puppet ChainState Block)
                     DeserialiseFailure
                     IO BSL.ByteString
codecPuppet =
    Puppet.codecPuppet
      CBOR.encode CBOR.decode
      CBOR.encode CBOR.decode -- this works?

mkLocalSocketAddrInfo :: FilePath -> Socket.AddrInfo
mkLocalSocketAddrInfo path =
    Socket.AddrInfo
      []
      Socket.AF_UNIX
      Socket.Stream
      Socket.defaultProtocol
      (Socket.SockAddrUnix path)
      Nothing
