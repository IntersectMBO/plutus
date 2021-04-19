module Env where

import Effect.AVar (AVar)
import Halogen (SubscriptionId)
import Plutus.PAB.Webserver (SPParams_)
import Servant.PureScript.Settings (SPSettings_)

-- Application enviroment configuration
type Env
  = { ajaxSettings :: SPSettings_ SPParams_
    -- FIXME: Add comment
    , contractStepCarouselSubscription :: AVar SubscriptionId
    }
