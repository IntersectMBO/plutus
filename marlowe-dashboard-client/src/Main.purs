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
import Marlowe (SPParams_(SPParams_))
import Servant.PureScript.Settings (SPSettingsDecodeJson_(..), SPSettingsEncodeJson_(..), SPSettings_(..), defaultSettings)

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
    driver <- runUI mainFrame unit body
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
