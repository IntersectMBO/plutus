{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}

module Cardano.Streaming.Callbacks where

import Cardano.Api qualified as C
import Cardano.Slotting.Slot (WithOrigin (At, Origin))
import Control.Exception (throw)
import Data.Word (Word16)
import Network.TypedProtocol.Pipelined (N (Z), Nat (Succ, Zero))
import Ouroboros.Network.Protocol.ChainSync.Client qualified as CS
import Ouroboros.Network.Protocol.ChainSync.ClientPipelined qualified as CSP
import Ouroboros.Network.Protocol.ChainSync.PipelineDecision (PipelineDecision (Collect),
                                                              pipelineDecisionMax)

import Cardano.Streaming.Helpers qualified as H

-- * Raw chain-sync clients using callback

blocksCallbackPipelined
  :: Word16
  -> C.LocalNodeConnectInfo
  -> C.ChainPoint
  -> (H.ChainSyncEvent C.BlockInMode -> IO ())
  -> IO ()
blocksCallbackPipelined n con point callback =
  C.connectToLocalNode con $
    C.LocalNodeClientProtocols
      { C.localChainSyncClient =
          C.LocalChainSyncClientPipelined $
            CSP.ChainSyncClientPipelined $
              pure $
                CSP.SendMsgFindIntersect [point] onIntersect
      , C.localTxSubmissionClient = Nothing
      , C.localStateQueryClient = Nothing
      , C.localTxMonitoringClient = Nothing
      }
 where
  onIntersect =
    CSP.ClientPipelinedStIntersect
      { CSP.recvMsgIntersectFound = \_ _ -> pure $ work n
      , CSP.recvMsgIntersectNotFound = throw H.NoIntersectionFound
      }

  work :: Word16 -> CSP.ClientPipelinedStIdle 'Z C.BlockInMode C.ChainPoint C.ChainTip IO ()
  work pipelineSize = requestMore Origin Origin Zero
   where
    requestMore -- was clientIdle_RequestMoreN
      :: WithOrigin C.BlockNo
      -> WithOrigin C.BlockNo
      -> Nat n
      -> CSP.ClientPipelinedStIdle n C.BlockInMode C.ChainPoint C.ChainTip IO ()
    requestMore clientTip serverTip rqsInFlight =
      let
       in case pipelineDecisionMax pipelineSize rqsInFlight clientTip serverTip of
            -- handle a response
            Collect -> case rqsInFlight of
              Succ predN -> CSP.CollectResponse Nothing (clientNextN predN)
            -- fire more requests
            _ ->
              CSP.SendMsgRequestNextPipelined
                (pure ())
                (requestMore clientTip serverTip (Succ rqsInFlight))

    clientNextN
      :: Nat n
      -> CSP.ClientStNext n C.BlockInMode C.ChainPoint C.ChainTip IO ()
    clientNextN rqsInFlight =
      CSP.ClientStNext
        { CSP.recvMsgRollForward = \bim ct -> do
            callback $ H.RollForward bim ct
            return $ requestMore (At $ H.bimBlockNo bim) (H.fromChainTip ct) rqsInFlight
        , CSP.recvMsgRollBackward = \cp ct -> do
            callback $ H.RollBackward cp ct
            return $ requestMore Origin (H.fromChainTip ct) rqsInFlight
        }

blocksCallback
  :: C.LocalNodeConnectInfo
  -> C.ChainPoint
  -> (H.ChainSyncEvent C.BlockInMode -> IO ())
  -> IO ()
blocksCallback con point callback =
  C.connectToLocalNode con $
    C.LocalNodeClientProtocols
      { C.localChainSyncClient =
          C.LocalChainSyncClient $
            CS.ChainSyncClient $
              pure $
                CS.SendMsgFindIntersect [point] onIntersect
      , C.localTxSubmissionClient = Nothing
      , C.localStateQueryClient = Nothing
      , C.localTxMonitoringClient = Nothing
      }
 where
  onIntersect =
    CS.ClientStIntersect
      { CS.recvMsgIntersectFound =
          \_ _ -> CS.ChainSyncClient sendRequestNext
      , CS.recvMsgIntersectNotFound = throw H.NoIntersectionFound
      }
  sendRequestNext =
    pure $
      CS.SendMsgRequestNext
        (pure ())
        CS.ClientStNext
          { CS.recvMsgRollForward = \bim ct -> CS.ChainSyncClient do
              callback $ H.RollForward bim ct
              sendRequestNext
          , CS.recvMsgRollBackward = \cp ct -> CS.ChainSyncClient do
              callback $ H.RollBackward cp ct
              sendRequestNext
          }
