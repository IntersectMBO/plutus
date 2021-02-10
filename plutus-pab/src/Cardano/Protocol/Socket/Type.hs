{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS -Wno-orphans           #-}
module Cardano.Protocol.Socket.Type where

import           Codec.Serialise.Class                              (Serialise)
import           Crypto.Hash                                        (SHA256, hash)
import           Data.Aeson                                         (FromJSON, ToJSON)
import qualified Data.ByteArray                                     as BA
import qualified Data.ByteString                                    as BS
import qualified Data.ByteString.Lazy                               as BSL
import           Data.Text.Prettyprint.Doc                          (Pretty)
import           Data.Typeable

import           GHC.Generics
import           NoThunks.Class                                     (NoThunks)

import           Codec.Serialise                                    (DeserialiseFailure)
import qualified Codec.Serialise                                    as CBOR
import           Network.TypedProtocol.Codec
import           Ouroboros.Network.Block                            (HeaderHash, Point, StandardHash)
import           Ouroboros.Network.Mux
import qualified Ouroboros.Network.Protocol.ChainSync.Codec         as ChainSync
import qualified Ouroboros.Network.Protocol.ChainSync.Type          as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Codec as TxSubmission
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Type  as TxSubmission
import           Ouroboros.Network.Util.ShowProxy

import           Ledger                                             (Block, Tx (..), TxId (..))
import           Ledger.Bytes                                       (LedgerBytes (..))

-- | Tip of the block chain type (used by node protocols).
type Tip = Block

-- | The node protocols require a block header type.
newtype BlockId = BlockId { getBlockId :: BS.ByteString }
  deriving (Eq, Ord, Generic)
  deriving anyclass (ToJSON, FromJSON)
  deriving newtype (Serialise, NoThunks)
  deriving (Pretty, Show) via LedgerBytes

-- | A hash of the block's contents.
blockId :: Block -> BlockId
blockId = BlockId
        . BA.convert
        . hash @_ @SHA256
        . BSL.toStrict
        . CBOR.serialise

-- | Explains why our (plutus) data structures are hashable.
type instance HeaderHash Tx = TxId
type instance HeaderHash Block = BlockId
deriving instance StandardHash Tx

-- TODO: Is this the best place for these instances?
instance ShowProxy Char
instance ShowProxy Tx where
instance ShowProxy a => ShowProxy [a] where
  showProxy _ = "[" ++ showProxy (Proxy @a) ++ "]"

deriving instance StandardHash Block
deriving newtype instance NoThunks TxId

-- | Limits for the protocols we use.
maximumMiniProtocolLimits :: MiniProtocolLimits
maximumMiniProtocolLimits =
    MiniProtocolLimits {
        maximumIngressQueue = maxBound
    }

-- | Packs up an application from the mini protocols we use.
-- This is used to build both a client and server application,
-- depending on the mini protocols passed as arguments.
nodeApplication
  :: RunMiniProtocol appType bytes m a b
  -> RunMiniProtocol appType bytes m a b
  -> OuroborosApplication appType addr bytes m a b
nodeApplication chainSync txSubmission =
    OuroborosApplication $ \_connectionId _shouldStopSTM -> [
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

type Offset = Integer

-- | Boilerplate codecs used for protocol serialisation.
codecChainSync :: Codec (ChainSync.ChainSync Block (Point Block) Tip)
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
