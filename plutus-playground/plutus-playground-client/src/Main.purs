module Main where

import Prelude

import Ace.Halogen.Component (AceEffects)
import Control.Monad.Aff.Console (CONSOLE)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Unsafe (unsafePerformEff)
import Control.Monad.Reader.Trans (runReaderT)
import Halogen (hoist)
import Halogen.Aff (HalogenEffects, awaitBody, runHalogenAff)
import Halogen.ECharts (EChartsEffects)
import Halogen.VDom.Driver (runUI)
import MainFrame (mainFrame)
import Network.HTTP.Affjax (AJAX)
import Playground.Server (SPParams_(SPParams_))

import Servant.PureScript.Settings (SPSettings_, defaultSettings)

ajaxSettings :: SPSettings_ SPParams_
ajaxSettings = defaultSettings $ SPParams_ { baseURL: "/api/" }

main :: Eff (HalogenEffects (EChartsEffects (AceEffects (console :: CONSOLE, ajax :: AJAX)))) Unit
main = runHalogenAff do
  body <- awaitBody
  runUI (hoist (flip runReaderT ajaxSettings) mainFrame) unit body

onLoad :: Unit
onLoad = unsafePerformEff main
