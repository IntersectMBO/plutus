{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

module Cardano.Protocol.Socket.Puppet.Codec where

import           Control.Monad.Class.MonadST

import qualified Codec.CBOR.Decoding                 as CBOR
import qualified Codec.CBOR.Encoding                 as CBOR
import qualified Codec.CBOR.Read                     as CBOR
import           Data.ByteString.Lazy                (ByteString)

import           Network.TypedProtocol.Codec.Cbor

import           Cardano.Protocol.Socket.Puppet.Type

codecPuppet
  :: forall state block m. MonadST m
  => (state -> CBOR.Encoding)
  -> (forall s . CBOR.Decoder s state)
  -> (block -> CBOR.Encoding)
  -> (forall s . CBOR.Decoder s block)
  -> Codec (Puppet state block) CBOR.DeserialiseFailure m ByteString
codecPuppet encodeState decodeState encodeBlock decodeBlock =
    mkCodecCborLazyBS encode decode
  where
    encode :: forall (pr :: PeerRole) st st'. PeerHasAgency pr st
           -> Message (Puppet state block) st st'
           -> CBOR.Encoding
    encode (ClientAgency TokIdle) MsgRequestState =
         CBOR.encodeListLen 1
      <> CBOR.encodeWord 0

    encode (ServerAgency TokBusy) (MsgReplyState state) =
         CBOR.encodeListLen 2
      <> CBOR.encodeWord 1
      <> encodeState state

    encode (ClientAgency TokIdle) MsgValidate =
         CBOR.encodeListLen 1
      <> CBOR.encodeWord 2

    encode (ServerAgency TokBusy) (MsgValidated block) =
         CBOR.encodeListLen 2
      <> CBOR.encodeWord 3
      <> encodeBlock block

    encode (ClientAgency TokIdle) MsgDone =
         CBOR.encodeListLen 1
      <> CBOR.encodeWord 4

    decode :: forall (pr :: PeerRole) s (st :: Puppet state block).
              PeerHasAgency pr st
           -> CBOR.Decoder s (SomeMessage st)
    decode stok = do
      len <- CBOR.decodeListLen
      key <- CBOR.decodeWord
      case (stok, len, key) of
        (ClientAgency TokIdle, 1, 0) -> return (SomeMessage MsgRequestState)
        (ServerAgency TokBusy, 2, 1) -> do
            state <- decodeState
            return (SomeMessage (MsgReplyState state))
        (ClientAgency TokIdle, 1, 2) -> return (SomeMessage MsgValidate)
        (ServerAgency TokBusy, 2, 3) -> do
            block <- decodeBlock
            return (SomeMessage (MsgValidated block))
        (ClientAgency TokIdle, 1, 4) -> return (SomeMessage MsgDone)
        _ -> fail ("puppet: unexpected key " ++ show (key, len))
