module Main where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, forkAff)
import Effect.Unsafe (unsafePerformEffect)
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.VDom.Driver (runUI)
import MainFrame (initialMainFrame)
import Plutus.SCB.Webserver.Types (StreamToClient, StreamToServer)
import Types (HAction(..), Query(..))
import WebSocket.Support (WebSocketManager, mkWebSocketManager)
import WebSocket.Support as WS

main :: Effect Unit
main = do
  runHalogenAff do
    body <- awaitBody
    driver <- runUI initialMainFrame Init body
    wsManager :: WebSocketManager StreamToClient StreamToServer <-
      mkWebSocketManager
    void
      $ forkAff
      $ WS.runWebSocketManager
          (WS.URI "/ws")
          (\msg -> void $ driver.query $ ReceiveWebSocketMessage msg unit)
          wsManager

onLoad :: Unit
onLoad = unsafePerformEffect main
