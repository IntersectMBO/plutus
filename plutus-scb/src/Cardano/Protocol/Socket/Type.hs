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
import qualified Data.ByteString.Lazy                               as BSL

import           Control.Concurrent.STM
import           GHC.Generics
import           Network.Socket                                     as Socket

import           Ouroboros.Network.Mux

import qualified Cardano.Protocol.Socket.Puppet.Codec               as Puppet
import qualified Cardano.Protocol.Socket.Puppet.Type                as Puppet
import           Codec.Serialise                                    (DeserialiseFailure)
import qualified Codec.Serialise                                    as CBOR
import           Network.TypedProtocol.Codec
import qualified Ouroboros.Network.Protocol.ChainSync.Codec         as ChainSync
import qualified Ouroboros.Network.Protocol.ChainSync.Type          as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Codec as TxSubmission
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Type  as TxSubmission

import           Cardano.Protocol.Node
import           Ledger                                             (Block, Tx (..))
import qualified Ledger.Index                                       as Index
import           Wallet.Emulator.Chain

-- CBOR Serialisation
deriving instance Generic Index.UtxoIndex
deriving newtype instance CBOR.Serialise Index.UtxoIndex
deriving instance Generic ChainState
deriving instance Serialise ChainState

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
