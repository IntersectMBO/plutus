module Main where

import Prologue
import AppM (runAppM)
import Capability.PlutusApps.MarloweApp as MarloweApp
import Control.Coroutine (Consumer, Process, connect, consumer, runProcess)
import Effect (Effect)
import Effect.AVar as AVar
import Effect.Aff (Aff, forkAff)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Unsafe (unsafePerformEffect)
import Env (DataProvider(..), Env, WebSocketManager)
import Foreign.Generic (defaultOptions)
import Halogen (hoist)
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.VDom.Driver (runUI)
import LocalStorage (RawStorageEvent)
import LocalStorage as LocalStorage
import MainFrame.State (mkMainFrame)
import MainFrame.Types (Action(..), Msg(..), Query(..))
import Plutus.PAB.Webserver (SPParams_(SPParams_))
import Servant.PureScript.Settings (SPSettingsDecodeJson_(..), SPSettingsEncodeJson_(..), SPSettings_(..), defaultSettings)
import WebSocket.Support as WS

mkEnvironment :: WebSocketManager -> Effect Env
mkEnvironment wsManager = do
  let
    SPSettings_ settings = defaultSettings $ SPParams_ { baseURL: "/" }

    jsonOptions = defaultOptions { unwrapSingleConstructors = true }

    decodeJson = SPSettingsDecodeJson_ jsonOptions

    encodeJson = SPSettingsEncodeJson_ jsonOptions
  contractStepCarouselSubscription <- AVar.empty
  marloweAppEndpointMutex <- MarloweApp.createEndpointMutex
  pure
    { ajaxSettings: SPSettings_ (settings { decodeJson = decodeJson, encodeJson = encodeJson })
    , contractStepCarouselSubscription
    , dataProvider: MarlowePAB
    , marloweAppEndpointMutex
    , wsManager
    }

main :: Effect Unit
main = do
  runHalogenAff do
    wsManager <- WS.mkWebSocketManager
    environment <- liftEffect $ mkEnvironment wsManager
    body <- awaitBody
    driver <- runUI (hoist (runAppM environment) mkMainFrame) Init body
    void
      $ forkAff
      $ runProcess watchLocalStorageProcess -- do we need this?
    ---
    void
      $ forkAff
      $ WS.runWebSocketManager
          (WS.URI "/ws")
          (\msg -> void $ forkAff $ driver.query $ ReceiveWebSocketMessage msg unit)
          wsManager
    driver.subscribe
      $ consumer
      $ case _ of
          -- This handler allows us to call an action in the MainFrame from a child component
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
