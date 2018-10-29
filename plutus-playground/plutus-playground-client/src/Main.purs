module Main where

import Prelude

import MainFrame (mainFrame)
import Effect (Effect)
import Effect.Unsafe (unsafePerformEffect)
import Halogen.Aff as HA
import Halogen.VDom.Driver (runUI)

main :: Effect Unit
main = HA.runHalogenAff do
  body <- HA.awaitBody
  runUI mainFrame unit body

onLoad :: Unit
onLoad = unsafePerformEffect main
