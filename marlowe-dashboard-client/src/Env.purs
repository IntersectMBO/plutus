module Env where

import Servant.PureScript.Settings (SPSettings_)
import Plutus.PAB.Webserver (SPParams_)

-- Application environment configuration
type Env
  = { ajaxSettings :: SPSettings_ SPParams_
    }
