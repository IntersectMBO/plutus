module Main where

import Prelude

import Ace.Halogen.Component (AceEffects)
import Control.Monad.Aff.Console (CONSOLE, log)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Unsafe (unsafePerformEff)
import Control.Monad.Except.Trans (runExceptT)
import Control.Monad.Reader.Trans (runReaderT)
import Halogen.Aff (HalogenEffects, awaitBody, runHalogenAff)
import Halogen.ECharts (EChartsEffects)
import Halogen.VDom.Driver (runUI)
import MainFrame (mainFrame)
import Network.HTTP.Affjax (AJAX)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Playground.Server (SPParams_(..), getVersion)
import Servant.PureScript.Affjax (errorToString)
import Servant.PureScript.Settings (SPSettings_, defaultSettings)

ajaxSettings :: SPSettings_ SPParams_
ajaxSettings = defaultSettings $ SPParams_ { baseURL: "/api/" }

main :: Eff (HalogenEffects (EChartsEffects (AceEffects (console :: CONSOLE, ajax :: AJAX)))) Unit
main = runHalogenAff do
  r <- RemoteData.fromEither <$> runExceptT (runReaderT getVersion ajaxSettings)
  case r of
    Failure err -> log $ errorToString err
    Success version -> log version
    Loading -> log "Loading"
    NotAsked -> log "NotAsked"
  body <- awaitBody
  runUI mainFrame unit body

onLoad :: Unit
onLoad = unsafePerformEff main
