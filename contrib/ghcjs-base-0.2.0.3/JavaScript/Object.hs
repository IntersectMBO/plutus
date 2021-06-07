{-# LANGUAGE UnboxedTuples #-}

module JavaScript.Object ( Object
                         , create
                         , getProp, unsafeGetProp
                         , setProp, unsafeSetProp
                         , allProps, listProps
                         , isInstanceOf
                         ) where



import           Data.JSString

import qualified JavaScript.Array as A

import qualified JavaScript.Array.Internal as AI
import           JavaScript.Object.Internal (Object(..))

import           JavaScript.Object.Internal -- as I

import           GHCJS.Types

{-
-- | create an empty object
create :: IO Object
create = fmap Object I.create
{-# INLINE create #-}

allProps :: Object -> IO (JSArray JSString)
allProps (Object o) = fmap AI.JSArray (I.allProps o)
{-# INLINE allProps #-}

listProps :: Object -> IO [JSString]
listProps (Object o) = I.listProps o
{-# INLINE listProps #-}

{- | get a property from an object. If accessing the property results in
     an exception, the exception is converted to a JSException. Since exception
     handling code prevents some optimizations in some JS engines, you may want
     to use unsafeGetProp instead
 -}
getProp :: JSString -> Object -> IO (JSVal a)
getProp p (Object o) = I.getProp p o
{-# INLINE getProp #-}

unsafeGetProp :: JSString -> Object -> IO (JSVal a)
unsafeGetProp p (Object o) = I.unsafeGetProp p o
{-# INLINE unsafeGetProp #-}

setProp :: JSString -> JSVal a -> Object -> IO ()
setProp p v (Object o) = I.setProp p v o
{-# INLINE setProp #-}

unsafeSetProp :: JSString -> JSVal a -> Object -> IO ()
unsafeSetProp p v (Object o) = I.unsafeSetProp p v o
{-# INLINE unsafeSetProp #-}

isInstanceOf :: Object -> JSVal a -> Bool
isInstanceOf (Object o) s = I.isInstanceOf o s
{-# INLINE isInstanceOf #-}
-}

-- -----------------------------------------------------------------------------
{-
foreign import javascript safe   "$2[$1]"
  js_getProp       :: JSString -> JSVal a -> IO (JSVal b)
foreign import javascript unsafe "$2[$1]"
  js_unsafeGetProp :: JSString -> JSVal a -> IO (JSVal b)
foreign import javascript safe   "$3[$1] = $2"
  js_setProp       :: JSString -> JSVal a -> JSVal b -> IO ()
foreign import javascript unsafe "$3[$1] = $2"
  js_unsafeSetProp :: JSString -> JSVal a -> JSVal b -> IO ()
foreign import javascript unsafe "$1 instanceof $2"
  js_isInstanceOf  :: Object -> JSVal a -> Bool
foreign import javascript unsafe  "h$allProps"
  js_allProps      :: Object -> IO (JSArray JSString)
foreign import javascript unsafe  "h$listProps"
  js_listProps     :: Object -> (# [JSString] #)
-}
