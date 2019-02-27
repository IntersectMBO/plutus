module Analytics
       ( trackEvent
       , Event
       , defaultEvent
       , ANALYTICS
       ) where

import Control.Monad.Eff (Eff, kind Effect)
import Data.Function.Uncurried (Fn4, runFn4)
import Data.Maybe (Maybe(..))
import Data.Undefinable (Undefinable, toUndefinable)
import Data.Unit (Unit)

foreign import data ANALYTICS :: Effect

foreign import trackEvent_ ::
  forall eff.
  Fn4 String (Undefinable String) (Undefinable String) (Undefinable Number) (Eff (analytics :: ANALYTICS | eff) Unit)

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

trackEvent :: forall eff. Event -> Eff (analytics :: ANALYTICS | eff) Unit
trackEvent {action, category, label, value} =
  runFn4 trackEvent_
    action
    (toUndefinable category)
    (toUndefinable label)
    (toUndefinable value)
