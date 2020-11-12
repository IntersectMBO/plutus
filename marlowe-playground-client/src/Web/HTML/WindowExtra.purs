-- This module contains helpers that should eventually be added into purescript-web-html
-- through a PR
module Web.HTML.WindowExtra
  ( close
  , postMessage
  ) where

import Prelude
import Effect (Effect)
import Effect.Uncurried as FU
import Foreign (Foreign)
import Web.HTML (Window)

foreign import _close :: FU.EffectFn1 Window Unit

close :: Window -> Effect Unit
close = FU.runEffectFn1 _close

foreign import _postMessage :: FU.EffectFn2 Foreign Window Unit

-- Post message dispatches a MessageEvent on a Window.
-- Browser documentation: https://developer.mozilla.org/en-US/docs/Web/API/Window/postMessage
-- TODO: targetOrigin and transfer are not being modeled, see if needed later
-- TODO: the message is whatever that can be serialized, for the moment I'm representing it with
--       foreing, validate if it's the right approach
postMessage :: Foreign -> Window -> Effect Unit
postMessage = FU.runEffectFn2 _postMessage
