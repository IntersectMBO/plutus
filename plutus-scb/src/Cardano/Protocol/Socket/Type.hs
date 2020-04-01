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

import           GHC.Generics
import           Network.Socket                                     as Socket

import           Ouroboros.Network.Mux

import           Codec.Serialise                                    (DeserialiseFailure)
import qualified Codec.Serialise                                    as CBOR
import           Network.TypedProtocol.Codec
import qualified Ouroboros.Network.Protocol.ChainSync.Codec         as ChainSync
import qualified Ouroboros.Network.Protocol.ChainSync.Type          as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Codec as TxSubmission
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Type  as TxSubmission

import           Cardano.Protocol                                   ()
import           Ledger                                             (Block, Tx (..))
import qualified Ledger.Index                                       as Index
import           Wallet.Emulator.Chain

-- CBOR Serialisation
deriving instance Generic Index.UtxoIndex
deriving newtype instance CBOR.Serialise Index.UtxoIndex
deriving instance Generic ChainState
deriving instance Serialise ChainState

type Tip = Block

data NodeToClientPtcls = LocalTxSubmissionPtcl
      deriving (Eq, Ord, Enum, Bounded, Show)

instance MiniProtocolLimits NodeToClientPtcls where
    maximumMessageSize _  = maxBound
    maximumIngressQueue _ = maxBound

instance ProtocolEnum NodeToClientPtcls where
    fromProtocolEnum LocalTxSubmissionPtcl   = MiniProtocolNum 3

type Offset = Int

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

mkLocalSocketAddrInfo :: FilePath -> Socket.AddrInfo
mkLocalSocketAddrInfo path =
    Socket.AddrInfo
      []
      Socket.AF_UNIX
      Socket.Stream
      Socket.defaultProtocol
      (Socket.SockAddrUnix path)
      Nothing
