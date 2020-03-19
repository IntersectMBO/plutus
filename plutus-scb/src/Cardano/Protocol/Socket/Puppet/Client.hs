{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes          #-}

module Cardano.Protocol.Socket.Puppet.Client where

import Network.TypedProtocol.Core

import Cardano.Protocol.Socket.Puppet.Type

newtype PuppetClient state block m a = PuppetClient {
    runPuppetClient :: m (PuppetClientStIdle state block m a)
  }

data PuppetClientStIdle state block m a where
  SendMsgRequestState
    :: (state -> m (PuppetClientStIdle state block m a))
    -> PuppetClientStIdle state block m a

  SendMsgValidate
    :: (block -> m (PuppetClientStIdle state block m a))
    -> PuppetClientStIdle state block m a

  SendMsgDone
    :: a -> PuppetClientStIdle state block m a

puppetClientPeer
  :: forall state block m a. Monad m
  => PuppetClient state block m a
  -> Peer (Puppet state block) 'AsClient 'StIdle m a
puppetClientPeer (PuppetClient client) =
    Effect $ go <$> client
  where
    go :: PuppetClientStIdle state block m a
       -> Peer (Puppet state block) 'AsClient 'StIdle m a
    go (SendMsgRequestState k) =
      Yield (ClientAgency TokIdle)
            MsgRequestState $
      Await (ServerAgency TokBusy) $ \msg -> case msg of
        MsgReplyState st -> Effect (go <$> k st)
        MsgValidated  _  -> error "Wrong answer to state request."

    go (SendMsgValidate k) =
      Yield (ClientAgency TokIdle)
            MsgValidate $
      Await (ServerAgency TokBusy) $ \msg -> case msg of
        MsgReplyState _    -> error "Wrong answer to validate request."
        MsgValidated block -> Effect (go <$> k block)

    go (SendMsgDone a) =
      Yield (ClientAgency TokIdle)
            MsgDone
            (Done TokDone a)
