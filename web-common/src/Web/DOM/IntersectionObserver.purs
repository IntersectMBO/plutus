-- This module provides FFI bindings for the Intersection Observer API.
-- https://www.w3.org/TR/intersection-observer/#intersection-observer-interface
-- TODO: Create a PR to make this a part of `purescript-web-dom`.
-- NOTE: I'm not using the uncurried package as `web-dom` doesn't use it either.
module Web.DOM.IntersectionObserver
  ( IntersectionObserver
  , IntersectionObserverEntry(..)
  , intersectionObserver
  , observe
  , unobserve
  , disconnect
  ) where

import Prelude
import Effect (Effect)
import Prim.Row (class Union)
import Web.DOM (Element)
import Web.HTML.HTMLElement (DOMRect)

foreign import data IntersectionObserver :: Type

type IntersectionObserverEntry
  = { target :: Element
    -- time :: DOMHighResTimeStamp
    -- rootBounds :: Nullable DOMRect
    , boundingClientRect :: DOMRect
    , intersectionRect :: DOMRect
    , isIntersecting :: Boolean
    , intersectionRatio :: Number
    }

type IntersectionObserverInitFields
  = ( {- NOTE: The spec says it can be a Element or Document. For the moment I choose
               Element for simplicity, maybe it would be a good idea to add a wrapper data
               ElementOrDocument
      -} root :: Element
    , rootMargin :: String
    {- NOTE: The spec says it can be a double or array of double. For the moment I choose
             only to manage a single Number for simplicity, maybe we would add a wrapper
             constructor
    -}
    , threshold :: Number
    )

foreign import intersectionObserver ::
  (Array IntersectionObserverEntry -> IntersectionObserver -> Effect Unit) ->
  Effect IntersectionObserver

foreign import _observe :: forall r. Element -> Record r -> IntersectionObserver -> Effect Unit

observe ::
  forall r rx.
  Union r rx IntersectionObserverInitFields =>
  Element ->
  Record r ->
  IntersectionObserver ->
  Effect Unit
observe = _observe

foreign import unobserve :: Element -> IntersectionObserver -> Effect Unit

foreign import disconnect :: IntersectionObserver -> Effect Unit
