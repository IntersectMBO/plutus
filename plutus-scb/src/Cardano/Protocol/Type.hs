{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS -Wno-orphans #-} -- TODO: remove this
module Cardano.Protocol.Type where

import qualified Data.ByteString.Lazy                               as LBS

import           Control.Concurrent.STM
import           Control.Lens                                       hiding (index)

import           GHC.Generics
import           Network.Socket                                     as Socket

import           Cardano.Slotting.Slot                              (SlotNo (..))
import           Ouroboros.Network.Block                            (HeaderHash, StandardHash)
import           Ouroboros.Network.Mux

import qualified Cardano.Protocol.Puppet.Codec                      as Puppet
import qualified Cardano.Protocol.Puppet.Type                       as Puppet
import qualified Ouroboros.Network.Protocol.ChainSync.Codec         as ChainSync
import qualified Ouroboros.Network.Protocol.ChainSync.Type          as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Codec as TxSubmission
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Type  as TxSubmission

import           Codec.Serialise                                    (DeserialiseFailure)
import qualified Codec.Serialise                                    as CBOR
import           Network.TypedProtocol.Codec

import           Ledger                                             (Block, Slot (..), Tx (..))
import qualified Ledger.Index                                       as Index
import qualified Wallet.Emulator.Chain                              as EC

-- Making plutus transaction representations work with the node protocols
type instance HeaderHash Tx = ()
type instance HeaderHash [Tx] = ()
deriving instance StandardHash Tx
deriving instance StandardHash [Tx]

deriving instance Generic Index.UtxoIndex
deriving newtype instance CBOR.Serialise Index.UtxoIndex
-- TODO: Review this.

type Tip = Block

data NodeToClientPtcls = ChainSyncWithBlocksPtcl
                       | LocalTxSubmissionPtcl
                       | PuppetPtcl
      deriving (Eq, Ord, Enum, Bounded, Show)

data ChainState =
     ChainState { _chainNewestFirst :: [(SlotNo, Block)]
                , _txPool           :: [Tx]
                , _index            :: Index.UtxoIndex
                } deriving (Show, Generic, CBOR.Serialise)

makeLenses ''ChainState

currentSlot :: ChainState -> Slot
currentSlot (ChainState [] _ _)                     = Slot 0
currentSlot (ChainState ((SlotNo slot, _) : _) _ _) =
  Slot $ toInteger slot

fromEChainState :: EC.ChainState -> ChainState
fromEChainState (EC.ChainState chain pool utxo (Slot s)) =
  ChainState { _chainNewestFirst = zip [slot ..] chain
             , _txPool = pool
             , _index  = utxo
             }
  where
    slot :: SlotNo
    slot =  fromIntegral $ s - toInteger (length chain)

toEChainState :: ChainState -> EC.ChainState
toEChainState s@(ChainState chain pool utxo) =
  EC.ChainState { EC._chainNewestFirst = map snd chain
                , EC._txPool = pool
                , EC._index  = utxo
                , EC._currentSlot = currentSlot s
                }

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
                        IO LBS.ByteString
codecChainSync =
    ChainSync.codecChainSync
      CBOR.encode (fmap const CBOR.decode)
      CBOR.encode             CBOR.decode
      CBOR.encode             CBOR.decode

codecTxSubmission :: Codec (TxSubmission.LocalTxSubmission Tx String)
                           DeserialiseFailure
                           IO LBS.ByteString
codecTxSubmission =
    TxSubmission.codecLocalTxSubmission
      CBOR.encode CBOR.decode
      CBOR.encode CBOR.decode

codecPuppet :: Codec (Puppet.Puppet ChainState Block)
                     DeserialiseFailure
                     IO LBS.ByteString
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
