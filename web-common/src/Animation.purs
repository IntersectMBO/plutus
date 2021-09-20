-- | An extremely primitive, but Halogen-5 compatible, animation system.
-- |
-- | To use:
-- |
-- | 1. Add a Boolean "is animating" flag to your state, and create a lens to that state.
-- |
-- | 2. In your Halogen `handleAction` function, instead of calling:
-- |
-- | ```purescript
-- | handleAction _ = do
-- |   stuff
-- |   thingThatNeedsToBeAnimated
-- |   stuff
-- |   ...
-- | ```
-- |
-- | ...call:
-- |
-- | ```purescript
-- | handleAction _ = do
-- |   stuff
-- |   animate _isAnimating thingThatNeedsToBeAnimated
-- |   stuff
-- |   ...
-- | ```
-- |
-- | 3. Mix `animationClass` into the HTML attributes of the thing to be animated (or a parent):
-- |
-- | ```purescript
-- | div
-- |   [ classes $
-- |       [ClassName "order"]
-- |       <>
-- |       animationClass _isAnimating state
-- |   ]
-- |   [ h3_ [ text "Your Order" ], ... ]
-- | ```
-- |
-- | 4. Add in CSS rules. When animating, the classes
-- |    `.animation.animation-start` will appear temporarily, to be replaced
-- |    moments later with `.animation.animation-done`. This allows you to use
-- |    SCSS such as:
-- |
-- | ```scss
-- | order.animation {
-- |   position: relative;
-- |
-- |   &.animation-start {
-- |     opacity: 0;
-- |     left: -100%;
-- |   }
-- |
-- |   &.animation-done {
-- |     transition: opacity 250ms, left 250ms;
-- |     opacity: 1;
-- |     left: 0;
-- | }
-- | ```
-- |
-- | ...making your `order` fade in from the left.
module Animation where

import Data.Lens (Lens', assign, view)
import Data.Time.Duration (Milliseconds(..))
import Data.Time.Duration as Duration
import Effect.Aff as Aff
import Effect.Aff.Class (class MonadAff, liftAff)
import Halogen (HalogenM)
import Halogen.HTML (ClassName(..))
import Prelude (bind, discard, pure, ($), (<>))

class MonadAnimate m state where
  animate :: forall a. (Lens' state Boolean) -> m a -> m a

instance monadAnimateHalogenM :: MonadAff m => MonadAnimate (HalogenM state action input output m) state where
  animate toggle action = do
    assign toggle true
    result <- action
    liftAff $ Aff.delay $ Duration.fromDuration $ Milliseconds 1.0
    assign toggle false
    pure result

animationClass :: forall state. Lens' state Boolean -> state -> Array ClassName
animationClass toggle state =
  [ ClassName "animation" ]
    <> if view toggle state then
        [ ClassName "animation-start" ]
      else
        [ ClassName "animation-done" ]
