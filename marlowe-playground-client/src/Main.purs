module Main where

import Prelude
import AppM (runAppM)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Unsafe (unsafePerformEffect)
import Env (Env)
import Foreign.Generic (defaultOptions)
import Halogen as H
import Halogen.Aff as HA
import Halogen.HTML as HH
import Halogen.VDom.Driver (runUI)
import MainFrame.State (component) as MainFrame
import MainFrame.Types (Query(..)) as MainFrame
import Marlowe (SPParams_(SPParams_))
import Router as Router
import Routing.Duplex as Routing
import Routing.Hash (matchesWith)
import Servant.PureScript.Settings (SPSettingsDecodeJson_(..), SPSettingsEncodeJson_(..), SPSettings_(..), defaultSettings)

environment :: Env
environment =
  { ajaxSettings: SPSettings_ (settings { decodeJson = decodeJson, encodeJson = encodeJson })
  }
  where
  SPSettings_ settings = defaultSettings $ SPParams_ { baseURL: "/" }

  jsonOptions = defaultOptions { unwrapSingleConstructors = true }

  decodeJson = SPSettingsDecodeJson_ jsonOptions

  encodeJson = SPSettingsEncodeJson_ jsonOptions

main ::
  Effect Unit
main =
  HA.runHalogenAff do
    body <- HA.awaitBody
    let
      mainFrame :: H.Component HH.HTML MainFrame.Query Unit Void Aff
      mainFrame = H.hoist (runAppM environment) MainFrame.component
    driver <- runUI mainFrame unit body
    void $ liftEffect
      $ matchesWith (Routing.parse Router.route) \old new -> do
          when (old /= Just new) $ launchAff_ $ driver.query (MainFrame.ChangeRoute new unit)

onLoad :: Unit
onLoad = unsafePerformEffect main
