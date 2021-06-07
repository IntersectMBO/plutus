{-# LANGUAGE ForeignFunctionInterface, JavaScriptFFI #-}

module JavaScript.Web.Canvas.ImageData ( ImageData
                                       , width
                                       , height
                                       , getData
                                       ) where

import JavaScript.TypedArray

import JavaScript.Web.Canvas.Internal

height :: ImageData -> Int
height i = js_height i
{-# INLINE height #-}

width :: ImageData -> Int
width i = js_width i
{-# INLINE width #-}

getData :: ImageData -> Uint8ClampedArray
getData i = js_getData i
{-# INLINE getData #-}

-- -----------------------------------------------------------------------------

foreign import javascript unsafe
  "$1.width" js_width :: ImageData -> Int
foreign import javascript unsafe
  "$1.height" js_height :: ImageData -> Int
foreign import javascript unsafe
  "$1.data" js_getData :: ImageData -> Uint8ClampedArray

