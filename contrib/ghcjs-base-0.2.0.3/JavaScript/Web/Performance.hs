{-# LANGUAGE ForeignFunctionInterface, JavaScriptFFI #-}

{- | The Performance interface represents timing-related performance information for the given page.
  -}

module JavaScript.Web.Performance
    ( now
    ) where

import GHCJS.Foreign.Callback
import GHCJS.Marshal.Pure
import GHCJS.Types

import Control.Exception (onException)
import Data.Typeable

{- | The 'now' computation returns a high resolution time stamp, measured in
     milliseconds, accurate to one thousandth of a millisecond.

     The value represented by 0 varies according the context, but
     in dedicated workers created from a Window context, the epoch is the value
     of the @PerformanceTiming.navigationStart@ property.
 -}
now :: IO Double
now = js_performanceNow
{-# INLINE now #-}

-- -----------------------------------------------------------------------------

foreign import javascript unsafe "performance.now()"
  js_performanceNow :: IO Double
