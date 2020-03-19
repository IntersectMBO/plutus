{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Protocol.Socket.Puppet.Server where

import Network.TypedProtocol.Core

import Cardano.Protocol.Socket.Puppet.Type

data PuppetServer state block m a =
     PuppetServer {
       recvMsgRequestState :: m (state, PuppetServer state block m a)
     , recvMsgValidate :: m (block, PuppetServer state block m a)
     , recvMsgDone :: a
     }

puppetServerPeer
  :: forall state block m a. Monad m
  => m (PuppetServer state block m a)
  -> Peer (Puppet state block) 'AsServer 'StIdle m a
puppetServerPeer server =
    Effect $ go <$> server
  where
    go :: PuppetServer state block m a
       -> Peer (Puppet state block) 'AsServer 'StIdle m a
    go PuppetServer{recvMsgRequestState, recvMsgValidate, recvMsgDone} =
      Await (ClientAgency TokIdle) $ \msg -> case msg of
        MsgRequestState -> Effect $ do
          (state, k) <- recvMsgRequestState
          return $ Yield
                     (ServerAgency TokBusy)
                     (MsgReplyState state)
                     (go k)

        MsgValidate -> Effect $ do
          (txs, k) <- recvMsgValidate
          return $ Yield
                     (ServerAgency TokBusy)
                     (MsgValidated txs)
                     (go k)

        MsgDone -> Done TokDone recvMsgDone
