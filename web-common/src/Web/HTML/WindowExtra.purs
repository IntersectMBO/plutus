-- This module contains helpers that should eventually be added into purescript-web-html
-- through a PR
module Web.HTML.WindowExtra
  ( close
  , postMessage
  , matchMedia
  , matches
  , MediaQueryList
  ) where

import Prelude
import Effect (Effect)
import Effect.Uncurried as FU
import Foreign (Foreign)
import Web.HTML (Window)

foreign import _close :: FU.EffectFn1 Window Unit

close :: Window -> Effect Unit
close = FU.runEffectFn1 _close

foreign import _postMessage :: FU.EffectFn3 Foreign String Window Unit

-- Post message dispatches a MessageEvent on a Window.
-- Browser documentation: https://developer.mozilla.org/en-US/docs/Web/API/Window/postMessage
-- TODO: transfer is not being modeled, see if needed later
postMessage :: Foreign -> String -> Window -> Effect Unit
postMessage = FU.runEffectFn3 _postMessage

---------
-- These functions allow the use of window.matchMedia
-- https://developer.mozilla.org/en-US/docs/Web/API/Window/matchMedia
foreign import data MediaQueryList :: Type

foreign import _matchMedia :: FU.EffectFn2 String Window MediaQueryList

matchMedia :: String -> Window -> Effect MediaQueryList
matchMedia = FU.runEffectFn2 _matchMedia

foreign import _matches :: FU.EffectFn1 MediaQueryList Boolean

matches :: MediaQueryList -> Effect Boolean
matches = FU.runEffectFn1 _matches
