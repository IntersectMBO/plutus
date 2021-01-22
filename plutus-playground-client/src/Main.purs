module Main where

import Control.Coroutine (Consumer, Process, connect, consumer, runProcess)
import Data.Maybe (Maybe(Nothing))
import Effect (Effect)
import Effect.Aff (Aff, forkAff)
import Effect.Class.Console (log)
import Effect.Unsafe (unsafePerformEffect)
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.VDom.Driver (runUI)
import LocalStorage (RawStorageEvent)
import LocalStorage as LocalStorage
import MainFrame.State (mkMainFrame)
import MainFrame.Types (HAction(..))
import Prelude (Unit, bind, discard, pure, show, ($), (<>))

main :: Effect Unit
main = do
  mainFrame <- mkMainFrame
  runHalogenAff do
    body <- awaitBody
    driver <- runUI mainFrame Mounted body
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
