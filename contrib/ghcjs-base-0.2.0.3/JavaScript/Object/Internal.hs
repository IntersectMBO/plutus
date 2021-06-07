{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE JavaScriptFFI #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE UnliftedFFITypes #-}

module JavaScript.Object.Internal
    ( Object(..)
    , create
    , allProps
    , listProps
    , getProp
    , unsafeGetProp
    , setProp
    , unsafeSetProp
    , isInstanceOf
    ) where

import           Data.JSString
import           Data.Typeable

import qualified GHCJS.Prim                as Prim
import           GHCJS.Types

import qualified JavaScript.Array          as JA
import           JavaScript.Array.Internal (JSArray, SomeJSArray(..))

import           Unsafe.Coerce
import qualified GHC.Exts as Exts

newtype Object = Object JSVal deriving (Typeable)
instance IsJSVal Object

-- | create an empty object
create :: IO Object
create = js_create
{-# INLINE create #-}

allProps :: Object -> IO JSArray
allProps o = js_allProps o
{-# INLINE allProps #-}

listProps :: Object -> IO [JSString]
listProps o = unsafeCoerce (js_listProps o)
{-# INLINE listProps #-}

{- | get a property from an object. If accessing the property results in
     an exception, the exception is converted to a JSException. Since exception
     handling code prevents some optimizations in some JS engines, you may want
     to use unsafeGetProp instead
 -}
getProp :: JSString -> Object -> IO JSVal
getProp p o = js_getProp p o
{-# INLINE getProp #-}

unsafeGetProp :: JSString -> Object -> IO JSVal
unsafeGetProp p o = js_unsafeGetProp p o
{-# INLINE unsafeGetProp #-}

setProp :: JSString -> JSVal -> Object -> IO ()
setProp p v o = js_setProp p v o
{-# INLINE setProp #-}

unsafeSetProp :: JSString -> JSVal -> Object -> IO ()
unsafeSetProp p v o = js_unsafeSetProp p v o
{-# INLINE unsafeSetProp #-}

isInstanceOf :: Object -> JSVal -> Bool
isInstanceOf o s = js_isInstanceOf o s
{-# INLINE isInstanceOf #-}

-- -----------------------------------------------------------------------------

foreign import javascript unsafe "$r = {};"
  js_create        :: IO Object
foreign import javascript safe   "$2[$1]"
  js_getProp       :: JSString -> Object -> IO JSVal
foreign import javascript unsafe "$2[$1]"
  js_unsafeGetProp :: JSString -> Object -> IO JSVal
foreign import javascript safe   "$3[$1] = $2"
  js_setProp       :: JSString -> JSVal -> Object -> IO ()
foreign import javascript unsafe "$3[$1] = $2"
  js_unsafeSetProp :: JSString -> JSVal -> Object -> IO ()
foreign import javascript unsafe "$1 instanceof $2"
  js_isInstanceOf  :: Object -> JSVal -> Bool
foreign import javascript unsafe  "h$allProps"
  js_allProps      :: Object -> IO JSArray
foreign import javascript unsafe  "h$listProps"
  js_listProps     :: Object -> IO Exts.Any -- [JSString]
