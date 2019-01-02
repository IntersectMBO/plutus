module Main where

import Prelude

import Ace.Halogen.Component (AceEffects)
import Analytics (ANALYTICS)
import Control.Coroutine (Consumer, Process, connect, consumer, runProcess)
import Control.Monad.Aff (forkAff, Aff)
import Control.Monad.Aff.Console (CONSOLE, log)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Unsafe (unsafePerformEff)
import Control.Monad.Reader.Trans (runReaderT)
import Data.Maybe (Maybe(..))
import Halogen (hoist)
import Halogen.Aff (HalogenEffects, awaitBody, runHalogenAff)
import Halogen.ECharts (EChartsEffects)
import Halogen.VDom.Driver (runUI)
import LocalStorage (LOCALSTORAGE, RawStorageEvent)
import LocalStorage as LocalStorage
import MainFrame (mainFrame)
import Network.HTTP.Affjax (AJAX)
import Playground.Server (SPParams_(SPParams_))
import Servant.PureScript.Settings (SPSettings_, defaultSettings)

ajaxSettings :: SPSettings_ SPParams_
ajaxSettings = defaultSettings $ SPParams_ { baseURL: "/api/" }

main :: Eff (HalogenEffects (EChartsEffects (AceEffects (console :: CONSOLE, ajax :: AJAX, analytics :: ANALYTICS, localStorage :: LOCALSTORAGE)))) Unit
main = runHalogenAff do
  body <- awaitBody
  driver <- runUI (hoist (flip runReaderT ajaxSettings) mainFrame) unit body
  forkAff $ runProcess watchLocalStorageProcess

watchLocalStorageProcess :: forall aff. Process (Aff (console :: CONSOLE, localStorage :: LOCALSTORAGE | aff)) Unit
watchLocalStorageProcess = connect LocalStorage.listen watchLocalStorage

watchLocalStorage :: forall aff r. Consumer RawStorageEvent (Aff (console :: CONSOLE | aff)) r
watchLocalStorage = consumer \event ->
  do log $ "Got Local Storage Event: " <> show event
     pure Nothing

onLoad :: Unit
onLoad = unsafePerformEff main
