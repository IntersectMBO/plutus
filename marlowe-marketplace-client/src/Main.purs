module Main where

import Prelude
import AppM (runAppM)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Unsafe (unsafePerformEffect)
import Env (Env)
import Halogen (Component, hoist)
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.HTML (HTML)
import Halogen.VDom.Driver (runUI)
import MainFrame.State (mkMainFrame)
import MainFrame.Types (Action(..))
import MainFrame.Types as MainFrame

environment :: Env
environment =
  { placeholder: "placeholder"
  }

main :: Effect Unit
main = do
  let
    mainFrame :: forall query msg. Component HTML query MainFrame.Action msg Aff
    mainFrame = hoist (runAppM environment) mkMainFrame
  runHalogenAff do
    body <- awaitBody
    driver <- runUI mainFrame Init body
    pure unit

onLoad :: Unit
onLoad = unsafePerformEffect main
