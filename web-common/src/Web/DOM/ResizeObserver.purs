-- This module provides FFI bindings for the Resize Observer API.
-- https://www.w3.org/TR/resize-observer/#api
-- TODO: Create a PR to make this a part of `purescript-web-dom`.
-- NOTE: I'm not using the uncurried package as `web-dom` doesn't use it either.
module Web.DOM.ResizeObserver
  ( ResizeObserver
  , ResizeObserverEntry(..)
  , ResizeObserverSize(..)
  , ResizeObserverBoxOptions(..)
  , resizeObserver
  , observe
  , unobserve
  , disconnect
  ) where

import Prelude
import Effect (Effect)
import Web.DOM (Element)
import Web.HTML.HTMLElement (DOMRect)

foreign import data ResizeObserver :: Type

type ResizeObserverSize
  = { inlineSize :: Number
    , blockSize :: Number
    }

type ResizeObserverEntry
  = { target :: Element
    , contentRect :: DOMRect
    , borderBoxSize :: ResizeObserverSize
    , contentBoxSize :: ResizeObserverSize
    , devicePixelContentBoxSize :: ResizeObserverSize
    }

data ResizeObserverBoxOptions
  = BorderBox
  | ContentBox
  | DevicePixelContentBox

optionsToFFI :: ResizeObserverBoxOptions -> String
optionsToFFI BorderBox = "border-box"

optionsToFFI ContentBox = "content-box"

optionsToFFI DevicePixelContentBox = "device-pixel-content-box"

foreign import resizeObserver ::
  (Array ResizeObserverEntry -> ResizeObserver -> Effect Unit) ->
  Effect ResizeObserver

foreign import _observe :: forall r. Element -> Record r -> ResizeObserver -> Effect Unit

observe ::
  Element ->
  ResizeObserverBoxOptions ->
  ResizeObserver ->
  Effect Unit
observe element options = _observe element { box: optionsToFFI options }

foreign import unobserve :: Element -> ResizeObserver -> Effect Unit

foreign import disconnect :: ResizeObserver -> Effect Unit
