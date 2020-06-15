module Main where

import Prelude
import Control.Coroutine (Consumer, Process, connect, consumer, runProcess, ($$))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff, forkAff, launchAff_)
import Control.Coroutine.Extra (mapConsumer)
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
import WebSocket (WebSocketResponseMessage)
import Types (HQuery(..), Message(..))
import WebSocket.Support (wsConsumer, wsProducer, wsSender, mkSocket)
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
  socket <- mkSocket "/api/ws"
  let
    mainFrame = mkMainFrame ajaxSettings
  runHalogenAff do
    body <- awaitBody
    driver <- runUI mainFrame unit body
    let
      handleWebSocket :: WS.Output WebSocketResponseMessage -> Aff Unit
      handleWebSocket msg = void $ driver.query $ ReceiveWebSocketMessage msg unit
    driver.subscribe
      $ mapConsumer (case _ of (WebSocketMessage msg) -> WS.SendMessage msg)
      $ wsSender handleWebSocket socket
    void $ forkAff $ runProcess (wsProducer socket $$ wsConsumer handleWebSocket)
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
