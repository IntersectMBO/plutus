module Main where

import Prelude

import AjaxUtils (ajaxSettings)
import Control.Coroutine (Consumer, Process, connect, consumer, runProcess)
import Control.Monad.Reader.Trans (runReaderT)
import Data.Maybe (Maybe(Nothing))
import Effect (Effect)
import Effect.Aff (Aff, forkAff)
import Effect.Class.Console (log)
import Effect.Unsafe (unsafePerformEffect)
import Halogen (hoist)
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.VDom.Driver (runUI)
import LocalStorage (RawStorageEvent)
import LocalStorage as LocalStorage
import MainFrame (mainFrame)

main :: Effect Unit
main = runHalogenAff do
  body <- awaitBody
  driver <- runUI (hoist (flip runReaderT ajaxSettings) mainFrame) unit body
  forkAff $ runProcess watchLocalStorageProcess

watchLocalStorageProcess :: Process Aff Unit
watchLocalStorageProcess = connect LocalStorage.listen watchLocalStorage

watchLocalStorage :: forall r. Consumer RawStorageEvent Aff r
watchLocalStorage = consumer \event ->
  do log $ "Got Local Storage Event: " <> show event
     pure Nothing

onLoad :: Unit
onLoad = unsafePerformEffect main
