module Main where

import Prelude
import Control.Coroutine (Consumer, Process, connect, consumer, runProcess)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff, forkAff)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Unsafe (unsafePerformEffect)
import Foreign.Generic (defaultOptions)
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.VDom.Driver (runUI)
import LocalStorage (RawStorageEvent)
import LocalStorage as LocalStorage
import MainFrame.State (mkMainFrame)
import MainFrame.Types (Action(..), Msg(..), Query(..))
import Marlowe (SPParams_(SPParams_))
import Servant.PureScript.Settings (SPSettingsDecodeJson_(..), SPSettingsEncodeJson_(..), SPSettings_(..), defaultSettings)
import WebSocket (StreamToClient, StreamToServer)
import WebSocket.Support (WebSocketManager, mkWebSocketManager)
import WebSocket.Support as WS

ajaxSettings :: SPSettings_ SPParams_
ajaxSettings = SPSettings_ $ (settings { decodeJson = decodeJson, encodeJson = encodeJson })
  where
  SPSettings_ settings = defaultSettings $ SPParams_ { baseURL: "/" }

  jsonOptions = defaultOptions { unwrapSingleConstructors = true }

  decodeJson = SPSettingsDecodeJson_ jsonOptions

  encodeJson = SPSettingsEncodeJson_ jsonOptions

main ::
  Effect Unit
main = do
  let
    mainFrame = mkMainFrame
  runHalogenAff do
    body <- awaitBody
    driver <- runUI mainFrame Init body
    void $ forkAff $ runProcess watchLocalStorageProcess
    wsManager :: WebSocketManager StreamToClient StreamToServer <- mkWebSocketManager
    void
      $ forkAff
      $ WS.runWebSocketManager (WS.URI "/ws") (\msg -> void $ driver.query $ ReceiveWebSocketMessage msg unit) wsManager
    driver.subscribe
      $ consumer
      $ case _ of
          (SendWebSocketMessage msg) -> do
            WS.managerWriteOutbound wsManager $ WS.SendMessage msg
            pure Nothing

watchLocalStorageProcess :: Process Aff Unit
watchLocalStorageProcess = connect LocalStorage.listen watchLocalStorage

watchLocalStorage ::
  forall r.
  Consumer RawStorageEvent Aff r
watchLocalStorage =
  consumer \event -> do
    liftEffect $ log $ "Got Local Storage Event: " <> show event
    pure Nothing

onLoad :: Unit
onLoad = unsafePerformEffect main
