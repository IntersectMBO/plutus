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
import Data.Generic (class Generic, GenericSpine(..), fromSpine, isValidSpine, toSignature, toSpine)
import Data.Maybe (Maybe(..), fromMaybe)
import FileEvents (FILE)
import Gist (GistId)
import Halogen (hoist)
import Halogen.Aff (HalogenEffects, awaitBody, runHalogenAff)
import Halogen.ECharts (EChartsEffects)
import Halogen.VDom.Driver (runUI)
import LocalStorage (LOCALSTORAGE, RawStorageEvent)
import LocalStorage as LocalStorage
import MainFrame (mainFrame)
import Network.HTTP.Affjax (AJAX)
import Meadow (SPParams_(SPParams_))
import Servant.PureScript.Settings (SPSettingsToUrlPiece_(..), SPSettings_(..), URLPiece, defaultSettings, gDefaultToURLPiece)
import Type.Proxy (Proxy(..))

ajaxSettings :: SPSettings_ SPParams_
ajaxSettings = SPSettings_ $ settings { toURLPiece = SPSettingsToUrlPiece_ gCustomToURLPiece }
  where
    SPSettings_ settings = defaultSettings $ SPParams_ { baseURL: "/api/" }

-- | Generally we want the default parameter encoding behaviour. But
-- sometimes we need to do something special.
gCustomToURLPiece :: forall a. Generic a => a -> URLPiece
gCustomToURLPiece v =
  fromMaybe (gDefaultToURLPiece v) $
  case toSpine v of
    SProd name [arg] ->
      if isInstanceOf (Proxy :: Proxy GistId) v
      then fromSpine $ arg unit
      else Nothing
    _ -> Nothing

isInstanceOf :: forall a b. Generic a => Generic b => Proxy a -> b -> Boolean
isInstanceOf proxy value =
  isValidSpine (toSignature proxy) (toSpine value)



main :: Eff (HalogenEffects (EChartsEffects (AceEffects (console :: CONSOLE, ajax :: AJAX, analytics :: ANALYTICS, localStorage :: LOCALSTORAGE, file :: FILE)))) Unit
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
