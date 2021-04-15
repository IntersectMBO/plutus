module Main where

import Prelude
import AppM (runAppM)
import Control.Coroutine (Consumer, Process, connect, consumer, runProcess)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff, forkAff)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Unsafe (unsafePerformEffect)
import Env (Env)
import Foreign.Generic (defaultOptions)
import Halogen (Component, hoist)
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.HTML (HTML)
import Halogen.VDom.Driver (runUI)
import LocalStorage (RawStorageEvent)
import LocalStorage as LocalStorage
import MainFrame.State (mkMainFrame)
import MainFrame.Types (Action(..), Msg(..), Query(..))
import MainFrame.Types as MainFrame
import Plutus.PAB.Webserver (SPParams_(SPParams_))
import Plutus.PAB.Webserver.Types (CombinedWSStreamToClient, CombinedWSStreamToServer)
import Servant.PureScript.Settings (SPSettingsDecodeJson_(..), SPSettingsEncodeJson_(..), SPSettings_(..), defaultSettings)
import WebSocket.Support (WebSocketManager, mkWebSocketManager)
import WebSocket.Support as WS

environment :: Env
environment =
  { ajaxSettings: SPSettings_ (settings { decodeJson = decodeJson, encodeJson = encodeJson })
  }
  where
  SPSettings_ settings = defaultSettings $ SPParams_ { baseURL: "/" }

  jsonOptions = defaultOptions { unwrapSingleConstructors = true }

  decodeJson = SPSettingsDecodeJson_ jsonOptions

  encodeJson = SPSettingsEncodeJson_ jsonOptions

main :: Effect Unit
main = do
  let
    mainFrame :: Component HTML MainFrame.Query MainFrame.Action MainFrame.Msg Aff
    mainFrame = hoist (runAppM environment) mkMainFrame
  runHalogenAff do
    body <- awaitBody
    driver <- runUI mainFrame Init body
    ---
    void
      $ forkAff
      $ runProcess watchLocalStorageProcess -- do we need this?
    ---
    wsManager :: WebSocketManager CombinedWSStreamToClient CombinedWSStreamToServer <-
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
          -- This handler allow us to call an action in the MainFrame from a child component
          -- (more info in the MainFrameLoop capability)
          (MainFrameActionMsg action) -> do
            void $ driver.query $ MainFrameActionQuery action unit
            pure Nothing

watchLocalStorageProcess :: Process Aff Unit
watchLocalStorageProcess = connect LocalStorage.listen watchLocalStorage

watchLocalStorage :: forall r. Consumer RawStorageEvent Aff r
watchLocalStorage =
  consumer \event -> do
    liftEffect $ log $ "Got Local Storage Event: " <> show event
    pure Nothing

onLoad :: Unit
onLoad = unsafePerformEffect main
