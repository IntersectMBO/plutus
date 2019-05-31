module Analytics
       ( trackEvent
       , Event
       , defaultEvent
       ) where

import Data.Function.Uncurried (Fn4, runFn4)
import Data.Maybe (Maybe(..))
import Data.Undefinable (Undefinable, toUndefinable)
import Data.Unit (Unit)
import Effect (Effect)

foreign import trackEvent_ ::
  Fn4 String (Undefinable String) (Undefinable String) (Undefinable Number) (Effect Unit)

type Event =
  { action :: String
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
trackEvent {action, category, label, value} =
  runFn4 trackEvent_
    action
    (toUndefinable category)
    (toUndefinable label)
    (toUndefinable value)
