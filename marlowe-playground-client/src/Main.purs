module Main where

import Prelude
import Control.Coroutine (Consumer, Process, connect, consumer, runProcess, ($$))
import Control.Monad.Reader.Trans (runReaderT)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (forkAff, Aff)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Unsafe (unsafePerformEffect)
import Foreign.Generic (defaultOptions)
import Halogen (hoist)
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.VDom.Driver (runUI)
import LocalStorage (RawStorageEvent)
import LocalStorage as LocalStorage
import MainFrame (mkMainFrame)
import Marlowe (SPParams_(SPParams_))
import Servant.PureScript.Settings (SPSettingsDecodeJson_(..), SPSettingsEncodeJson_(..), SPSettings_(..), defaultSettings)
import Web.HTML as W
import Web.HTML.Location as WL
import Web.HTML.Window as WW
import Web.Socket.WebSocket as WS
import Websockets (wsConsumer, wsProducer, wsSender)

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
  window <- W.window
  location <- WW.location window
  protocol <- WL.protocol location
  hostname <- WL.hostname location
  port <- WL.port location
  let
    wsProtocol = case protocol of
      "https:" -> "wss"
      _ -> "ws"

    wsPath = wsProtocol <> "://" <> hostname <> ":" <> port <> "/api/ws"
  socket <- WS.create wsPath []
  mainFrame <- mkMainFrame
  runHalogenAff do
    body <- awaitBody
    driver <- runUI (hoist (flip runReaderT ajaxSettings) mainFrame) unit body
    driver.subscribe $ wsSender socket driver.query
    void $ forkAff $ runProcess (wsProducer socket $$ wsConsumer driver.query)
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
