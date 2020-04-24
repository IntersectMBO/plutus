module Main where

import Prelude
import Effect (Effect)
import Effect.Unsafe (unsafePerformEffect)
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.VDom.Driver (runUI)
import MainFrame (initialMainFrame)
import Types (HAction(..))

main :: Effect Unit
main = do
  runHalogenAff do
    body <- awaitBody
    driver <- runUI initialMainFrame Init body
    pure unit

onLoad :: Unit
onLoad = unsafePerformEffect main
