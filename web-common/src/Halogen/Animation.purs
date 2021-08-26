-- This module offers some helpers for using Tailwind animations with halogen using the Web Animation API
-- https://developer.mozilla.org/en-US/docs/Web/API/Web_Animations_API
module Halogen.Animation where

import Prelude
import Control.Promise (Promise, toAffE)
import Data.Array (filter)
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Effect.Uncurried (EffectFn1, EffectFn2, runEffectFn1, runEffectFn2)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import Web.DOM.DOMTokenList as DOMTokenList
import Web.HTML (HTMLElement)
import Web.HTML.HTMLElement (classList)

foreign import data CSSAnimation :: Type

foreign import getAnimations_ :: EffectFn1 HTMLElement (Array CSSAnimation)

foreign import getAnimationName :: CSSAnimation -> String

foreign import setOnFinishHandler_ :: EffectFn2 CSSAnimation (Effect Unit) Unit

foreign import animationFinished_ :: EffectFn1 CSSAnimation (Promise Unit)

getAnimations :: HTMLElement -> Effect (Array CSSAnimation)
getAnimations = runEffectFn1 getAnimations_

-- The feautre is experimental and is not supported on Internet Explorer.
-- https://developer.mozilla.org/en-US/docs/Web/API/Animation/onfinish
setOnFinishHandler :: CSSAnimation -> Effect Unit -> Effect Unit
setOnFinishHandler = runEffectFn2 setOnFinishHandler_

-- The Animation.finished returns a Promise which resolves once the animation has finished playing.
-- The feautre is experimental and is not supported on Internet Explorer.
-- https://developer.mozilla.org/en-US/docs/Web/API/Animation/finished
animationFinished :: CSSAnimation -> Aff Unit
animationFinished = toAffE <<< runEffectFn1 animationFinished_

-- This function adds a tailwind animation `animationName` (which can be customized using CSS Animations)
-- to an element, and calls an `action` once it finished. The only way to call HalogenM from the Effect world
-- is via the subscriptions mechanism, so you need to subscribe to this EventSource.
-- You don't need to unsubscribe as the EventSource closes itself after firing the action.
-- https://tailwindcss.com/docs/animation
animateAndWaitUntilFinishSubscription ::
  forall m action.
  MonadAff m =>
  String ->
  action ->
  HTMLElement ->
  EventSource m action
animateAndWaitUntilFinishSubscription animationName action element =
  EventSource.effectEventSource \emitter -> do
    let
      className = "animate-" <> animationName
    -- Adding the class to the element starts the animation
    classes <- classList element
    DOMTokenList.add classes className
    animations <- getAnimations element <#> filter (\animation -> animationName == getAnimationName animation)
    let
      cb :: Effect Unit
      cb = do
        EventSource.emit emitter action
        EventSource.close emitter
        -- We remove the css class so we can redo the animation if necessary
        DOMTokenList.remove classes className
    case animations of
      [ animation ] -> setOnFinishHandler animation cb
      _ -> cb
    pure $ EventSource.Finalizer mempty

-- same as `animateAndWaitUntilFinishSubscription` but works with Aff instead of subscriptions so it allows
-- to sequence animations.
animateAndWaitUntilFinish ::
  String ->
  HTMLElement ->
  Aff Unit
animateAndWaitUntilFinish animationName element = do
  let
    className = "animate-" <> animationName

    getAnimations' = liftEffect <<< getAnimations
  -- Adding the class to the element starts the animation
  classes <- liftEffect $ classList element
  liftEffect $ DOMTokenList.add classes className
  animations <- getAnimations' element <#> filter (\animation -> animationName == getAnimationName animation)
  -- TODO: Try to use `finally` to make sure the class is removed even if we kill the Aff ("cancel animation")
  case animations of
    [ animation ] -> animationFinished animation
    _ -> pure unit
  -- We remove the css class so we can redo the animation if necessary
  liftEffect $ DOMTokenList.remove classes className

waitForAllAnimations :: HTMLElement -> Aff Unit
waitForAllAnimations element = do
  animations <- liftEffect $ getAnimations element
  void $ traverse animationFinished animations
