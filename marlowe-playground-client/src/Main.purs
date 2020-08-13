module Main where

import Prelude
import Control.Coroutine (Consumer, Process, connect, consumer, runProcess)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff, forkAff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Unsafe (unsafePerformEffect)
import Foreign.Generic (defaultOptions)
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.VDom.Driver (runUI)
import LocalStorage (RawStorageEvent)
import LocalStorage as LocalStorage
import MainFrame (mkMainFrame)
import Marlowe (SPParams_(SPParams_))
import Router as Router
import Routing.Duplex as Routing
import Routing.Hash (matchesWith)
import Servant.PureScript.Settings (SPSettingsDecodeJson_(..), SPSettingsEncodeJson_(..), SPSettings_(..), defaultSettings)
import WebSocket (WebSocketRequestMessage, WebSocketResponseMessage)
import Types (HQuery(..))
import WebSocket.Support (WebSocketManager)
import WebSocket.Support as WS

ajaxSettings :: SPSettings_ SPParams_
ajaxSettings = SPSettings_ $ (settings { decodeJson = decodeJson, encodeJson = encodeJson })
  where
  SPSettings_ settings = defaultSettings $ SPParams_ { baseURL: "/api/" }

  jsonOptions = defaultOptions { unwrapSingleConstructors = true }

  decodeJson = SPSettingsDecodeJson_ jsonOptions

  encodeJson = SPSettingsEncodeJson_ jsonOptions

main ::
  Effect Unit
main = do
  let
    mainFrame = mkMainFrame ajaxSettings
  runHalogenAff do
    body <- awaitBody
    driver <- runUI mainFrame unit body
    wsManager :: WebSocketManager WebSocketResponseMessage WebSocketRequestMessage <- WS.mkWebSocketManager
    void
      $ forkAff
      $ WS.runWebSocketManager
          (WS.URI "/api/ws")
          (\msg -> void $ driver.query $ ReceiveWebSocketMessage msg unit)
          wsManager
    void $ liftEffect
      $ matchesWith (Routing.parse Router.route) \old new -> do
          when (old /= Just new) $ launchAff_ $ driver.query (ChangeRoute new unit)
    forkAff $ runProcess watchLocalStorageProcess

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
