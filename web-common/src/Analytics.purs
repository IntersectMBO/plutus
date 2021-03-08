module Analytics
  ( Event
  , SegmentEvent
  , defaultEvent
  , class IsEvent
  , toEvent
  , analyticsTracking
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Traversable (for_)
import Data.Tuple.Nested ((/\))
import Data.Undefinable (Undefinable, toUndefinable)
import Effect (Effect)
import Effect.Uncurried (EffectFn2, EffectFn4, runEffectFn2, runEffectFn4)
import Foreign (Foreign, unsafeToForeign)
import Foreign.NullOrUndefined (null)
import Foreign.Object (Object)
import Foreign.Object as Object

foreign import trackEvent_ ::
  EffectFn4 String (Undefinable String) (Undefinable String) (Undefinable Number) Unit

foreign import trackSegmentEvent_ ::
  EffectFn2 String (Object Foreign) Unit

type Event
  = { action :: String
    , category :: Maybe String
    , label :: Maybe String
    , value :: Maybe Number
    }

type SegmentEvent
  = { action :: String
    , payload :: Object Foreign
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

trackSegmentEvent :: SegmentEvent -> Effect Unit
trackSegmentEvent { action, payload } = runEffectFn2 trackSegmentEvent_ action payload

class IsEvent a where
  toEvent :: a -> Maybe Event

toSegmentEvent :: Event -> SegmentEvent
toSegmentEvent { action, category, label, value } =
  { action
  , payload:
      Object.fromFoldable
        [ "category" /\ toForeign category
        , "label" /\ toForeign label
        , "value" /\ toForeign value
        ]
  }

analyticsTracking :: forall a. IsEvent a => a -> Effect Unit
analyticsTracking action = do
  for_ (toEvent action)
    $ \event -> do
        trackEvent event
        trackSegmentEvent $ toSegmentEvent event

------------------------------------------------------------
-- This `IsForeign` code only exists because we need to use
-- `unsafeToForeign`, but we want to limit it to types we know are safe.
--
-- As the docs say, "[unsafeToForeign] is considered unsafe as it's
-- only intended to be used on primitive JavaScript types, rather than
-- PureScript types." So it's safe as long as you use it on the right
-- types.
class IsForeign a where
  toForeign :: a -> Foreign

instance toForeignMaybe :: IsForeign a => IsForeign (Maybe a) where
  toForeign Nothing = null
  toForeign (Just x) = toForeign x

instance toForeignString :: IsForeign String where
  toForeign = unsafeToForeign

instance toForeignNumber :: IsForeign Number where
  toForeign = unsafeToForeign
