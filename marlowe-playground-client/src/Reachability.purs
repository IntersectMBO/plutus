module Reachability (startReachabilityAnalysis, updateWithResponse) where

import Foreign.Generic (encode, encodeJSON)
import Global.Unsafe (unsafeStringify)
import Halogen as H
import Halogen (HalogenM)
import Marlowe.Symbolic.Types.Response (Result)
import Network.RemoteData (RemoteData(..))
import Prelude (Unit, discard, pure, ($), (<<<))
import Marlowe.Semantics (Contract)
import Marlowe.Semantics as S
import Simulation.Types (Action, ChildSlots, Message(..), ReachabilityAnalysisData, State)
import WebSocket (WebSocketRequestMessage(..))

checkContractForReachability :: forall m. String -> String -> HalogenM State Action ChildSlots Message m Unit
checkContractForReachability contract state = H.raise (WebsocketMessage msgString)
  where
  msgString = unsafeStringify <<< encode $ CheckForWarnings (encodeJSON true) contract state

startReachabilityAnalysis :: forall m. Contract -> S.State -> HalogenM State Action ChildSlots Message m ReachabilityAnalysisData
startReachabilityAnalysis contract state = do
  checkContractForReachability (encodeJSON contract) (encodeJSON state)
  pure { remoteData: Loading }

updateWithResponse :: forall m. ReachabilityAnalysisData -> RemoteData String Result -> HalogenM State Action ChildSlots Message m ReachabilityAnalysisData
updateWithResponse state response = pure (state { remoteData = response })
