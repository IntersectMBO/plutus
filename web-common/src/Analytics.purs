module Analytics
  ( trackEvent
  , Event
  , defaultEvent
  , class IsEvent
  , toEvent
  , analyticsTracking
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Undefinable (Undefinable, toUndefinable)
import Data.Unit (Unit)
import Effect (Effect)
import Effect.Uncurried (EffectFn4, runEffectFn4)

foreign import trackEvent_ ::
  EffectFn4 String (Undefinable String) (Undefinable String) (Undefinable Number) Unit

type Event
  = { action :: String
    , category :: Maybe String
    , label :: Maybe String
    , value :: Maybe Number
    }

defaultEvent :: String -> Event
defaultEvent action =
  { action
  , category: Nothing
  , label: Nothing
  , value: Nothing
  }

trackEvent :: Event -> Effect Unit
trackEvent { action, category, label, value } =
  runEffectFn4 trackEvent_
    action
    (toUndefinable category)
    (toUndefinable label)
    (toUndefinable value)

class IsEvent a where
  toEvent :: a -> Maybe Event

analyticsTracking :: forall a. IsEvent a => a -> Effect Unit
analyticsTracking action = do
  case toEvent action of
    Nothing -> pure unit
    Just event -> trackEvent event
