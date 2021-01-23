module Main where

import Prelude
import Control.Coroutine (consumer)
import Data.Maybe (Maybe(Nothing))
import Effect (Effect)
import Effect.Aff (forkAff)
import Effect.Unsafe (unsafePerformEffect)
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.VDom.Driver (runUI)
import MainFrame (initialMainFrame)
import Plutus.PAB.Webserver.Types (StreamToClient, StreamToServer)
import Types (HAction(..), Query(..), Output(..))
import WebSocket.Support (WebSocketManager, mkWebSocketManager)
import WebSocket.Support as WS

main :: Effect Unit
main = do
  runHalogenAff do
    body <- awaitBody
    driver <- runUI initialMainFrame Init body
    --
    wsManager :: WebSocketManager StreamToClient StreamToServer <-
      mkWebSocketManager
    void
      $ forkAff
      $ WS.runWebSocketManager
          (WS.URI "/ws")
          (\msg -> void $ driver.query $ ReceiveWebSocketMessage msg unit)
          wsManager
    driver.subscribe
      $ consumer
      $ case _ of
          (SendWebSocketMessage msg) -> do
            WS.managerWriteOutbound wsManager $ WS.SendMessage msg
            pure Nothing

onLoad :: Unit
onLoad = unsafePerformEffect main
