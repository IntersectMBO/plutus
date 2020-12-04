module Halogen.Analytics where

import Prelude

import Analytics (class IsEvent, analyticsTracking)
import Effect.Class (class MonadEffect, liftEffect)
import Halogen (HalogenM)
import Prim.TypeError (class Warn, Text)

handleActionWithAnalyticsTracking ::
  forall state action slots message m a.
  Warn (Text "TODO: Rename handleActionWithAnalyticsTracking to withAnalytics") =>
  MonadEffect m =>
  IsEvent action =>
  (action -> HalogenM state action slots message m a) -> action -> HalogenM state action slots message m a
handleActionWithAnalyticsTracking handleAction' action = do
  liftEffect $ analyticsTracking action
  handleAction' action
