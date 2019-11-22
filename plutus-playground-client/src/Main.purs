module Main where

import Prelude
import Control.Coroutine (Consumer, Process, connect, consumer, runProcess)
import Control.Monad.Except (runExcept)
import Control.Monad.Reader.Trans (runReaderT)
import Data.Either (Either(..))
import Data.Maybe (Maybe(Nothing))
import Effect (Effect)
import Effect.Aff (Aff, forkAff)
import Effect.Class.Console (log)
import Effect.Console (logShow)
import Effect.Unsafe (unsafePerformEffect)
import Halogen (hoist)
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.VDom.Driver (runUI)
import LocalStorage (RawStorageEvent)
import LocalStorage as LocalStorage
import MainFrame (mkMainFrame)
import Playground.Server (SPParams_(..))
import Servant.PureScript.Settings (SPSettings_, defaultSettings)
import Types (HAction(..))

ajaxSettings :: SPSettings_ SPParams_
ajaxSettings = defaultSettings $ SPParams_ { baseURL: "/api/" }

main :: Effect Unit
main = do
  case runExcept mkMainFrame of
    Left err -> logShow err
    Right mainFrame ->
      runHalogenAff do
        body <- awaitBody
        driver <- runUI (hoist (flip runReaderT ajaxSettings) mainFrame) Mounted body
        forkAff $ runProcess watchLocalStorageProcess

watchLocalStorageProcess :: Process Aff Unit
watchLocalStorageProcess = connect LocalStorage.listen watchLocalStorage

watchLocalStorage :: forall r. Consumer RawStorageEvent Aff r
watchLocalStorage =
  consumer \event -> do
    log $ "Got Local Storage Event: " <> show event
    pure Nothing

onLoad :: Unit
onLoad = unsafePerformEffect main
