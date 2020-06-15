module Main where

import Prelude
import Control.Coroutine (connect, runProcess)
import Control.Coroutine.Extra (mapConsumer)
import Effect (Effect)
import Effect.Aff (Aff, forkAff)
import Effect.Unsafe (unsafePerformEffect)
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.VDom.Driver (runUI)
import MainFrame (initialMainFrame)
import Plutus.SCB.Types (ContractExe)
import Plutus.SCB.Webserver.Types (StreamToClient)
import Types (HAction(..), Output(..), Query(..))
import WebSocket.Support (mkSocket, Output) as WS
import WebSocket.Support (wsConsumer, wsProducer, wsSender)

main :: Effect Unit
main = do
  socket <- WS.mkSocket "/ws"
  runHalogenAff do
    body <- awaitBody
    driver <- runUI initialMainFrame Init body
    let
      handleWebSocket :: WS.Output (StreamToClient ContractExe) -> Aff Unit
      handleWebSocket msg = void $ driver.query $ ReceiveWebSocketMessage msg unit
    void $ forkAff
      $ runProcess
      $ connect
          (wsProducer socket)
          (wsConsumer handleWebSocket)
    driver.subscribe
      $ mapConsumer (case _ of (SendWebSocketMessage msg) -> msg)
      $ wsSender handleWebSocket socket

onLoad :: Unit
onLoad = unsafePerformEffect main
