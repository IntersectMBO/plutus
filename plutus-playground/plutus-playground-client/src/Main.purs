module Main where

import Prelude

import Ace.Halogen.Component (AceEffects)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE)
import Control.Monad.Eff.Unsafe (unsafePerformEff)
import Halogen.Aff (HalogenEffects, awaitBody, runHalogenAff)
import Halogen.VDom.Driver (runUI)
import MainFrame (mainFrame)

main :: Eff (HalogenEffects (AceEffects (console :: CONSOLE))) Unit
main = runHalogenAff do
  body <- awaitBody
  runUI mainFrame unit body

onLoad :: Unit
onLoad = unsafePerformEff main
