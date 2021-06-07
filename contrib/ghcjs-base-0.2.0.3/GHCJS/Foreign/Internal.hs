{-# LANGUAGE ForeignFunctionInterface, UnliftedFFITypes, JavaScriptFFI,
    UnboxedTuples, DeriveDataTypeable, GHCForeignImportPrim,
    MagicHash, FlexibleInstances, BangPatterns, Rank2Types, CPP #-}

{- | Basic interop between Haskell and JavaScript.

     The principal type here is 'JSVal', which is a lifted type that contains
     a JavaScript reference. The 'JSVal' type is parameterized with one phantom
     type, and GHCJS.Types defines several type synonyms for specific variants.

     The code in this module makes no assumptions about 'JSVal a' types.
     Operations that can result in a JS exception that can kill a Haskell thread
     are marked unsafe (for example if the 'JSVal' contains a null or undefined
     value). There are safe variants where the JS exception is propagated as
     a Haskell exception, so that it can be handled on the Haskell side.

     For more specific types, like 'JSArray' or 'JSBool', the code assumes that
     the contents of the 'JSVal' actually is a JavaScript array or bool value.
     If it contains an unexpected value, the code can result in exceptions that
     kill the Haskell thread, even for functions not marked unsafe.

     The code makes use of `foreign import javascript', enabled with the
     `JavaScriptFFI` extension, available since GHC 7.8. There are three different
     safety levels:

      * unsafe: The imported code is run directly. returning an incorrectly typed
        value leads to undefined behaviour. JavaScript exceptions in the foreign
        code kill the Haskell thread.
      * safe: Returned values are replaced with a default value if they have
        the wrong type. JavaScript exceptions are caught and propagated as
        Haskell exceptions ('JSException'), so they can be handled with the
        standard "Control.Exception" machinery.
      * interruptible: The import is asynchronous. The calling Haskell thread
        sleeps until the foreign code calls the `$c` JavaScript function with
        the result. The thread is in interruptible state while blocked, so it
        can receive asynchronous exceptions.

     Unlike the FFI for native code, it's safe to call back into Haskell
     (`h$run`, `h$runSync`) from foreign code in any of the safety levels.
     Since JavaScript is single threaded, no Haskell threads can run while
     the foreign code is running.
 -}

module GHCJS.Foreign.Internal ( JSType(..)
                              , jsTypeOf
                              , JSONType(..)
                              , jsonTypeOf
                              -- , mvarRef
                              , isTruthy
                              , fromJSBool
                              , toJSBool
                              , jsTrue
                              , jsFalse
                              , jsNull
                              , jsUndefined
                              , isNull
                              -- type predicates
                              , isUndefined
                              , isNumber
                              , isObject
                              , isBoolean
                              , isString
                              , isSymbol
                              , isFunction
                                -- internal use, fixme remove
{-                              , toArray
                              , newArray
                              , fromArray
                              , pushArray
                              , indexArray
                              , lengthArray -}
--                              , newObj
--                              , js_getProp, js_unsafeGetProp
--                              , js_setProp, js_unsafeSetProp
--                              , listProps
{-                              , wrapBuffer, wrapMutableBuffer
                              , byteArrayJSVal, mutableByteArrayJSVal
                              , bufferByteString, byteArrayByteString
                              , unsafeMutableByteArrayByteString -}
                              ) where

import           GHCJS.Types
import qualified GHCJS.Prim as Prim

import           GHC.Prim
import           GHC.Exts

import           Control.Applicative
import           Control.Concurrent.MVar
import           Control.DeepSeq (force)
import           Control.Exception (evaluate, Exception)

import           Foreign.ForeignPtr.Safe
import           Foreign.Ptr

import           Data.Primitive.ByteArray
import           Data.Typeable (Typeable)

import           Data.ByteString (ByteString)
import           Data.ByteString.Unsafe (unsafePackAddressLen)

import qualified Data.Text.Array as A
import qualified Data.Text as T
import qualified Data.Text.Internal as T
import qualified Data.Text.Lazy as TL (Text, toStrict, fromStrict)

import           Unsafe.Coerce

-- types returned by JS typeof operator
data JSType = Undefined
            | Object
            | Boolean
            | Number
            | String
            | Symbol
            | Function
            | Other    -- ^ implementation dependent
            deriving (Show, Eq, Ord, Enum, Typeable)

-- JSON value type
data JSONType = JSONNull
              | JSONInteger
              | JSONFloat
              | JSONBool
              | JSONString
              | JSONArray
              | JSONObject
              deriving (Show, Eq, Ord, Enum, Typeable)

fromJSBool :: JSVal -> Bool
fromJSBool b = js_fromBool b
{-# INLINE fromJSBool #-}

toJSBool :: Bool -> JSVal
toJSBool True = jsTrue
toJSBool _    = jsFalse
{-# INLINE toJSBool #-}

jsTrue :: JSVal
jsTrue = mkRef (js_true 0#)
{-# INLINE jsTrue #-}

jsFalse :: JSVal
jsFalse = mkRef (js_false 0#)
{-# INLINE jsFalse #-}

jsNull :: JSVal
jsNull = mkRef (js_null 0#)
{-# INLINE jsNull #-}

jsUndefined :: JSVal
jsUndefined = mkRef (js_undefined 0#)
{-# INLINE jsUndefined #-}

-- check whether a reference is `truthy' in the JavaScript sense
isTruthy :: JSVal -> Bool
isTruthy b = js_isTruthy b
{-# INLINE isTruthy #-}

-- isUndefined :: JSVal -> Bool
-- isUndefined o = js_isUndefined o
-- {-# INLINE isUndefined #-}

-- isNull :: JSVal -> Bool
-- isNull o = js_isNull o
-- {-# INLINE isNull #-}

isObject :: JSVal -> Bool
isObject o = js_isObject o
{-# INLINE isObject #-}

isNumber :: JSVal -> Bool
isNumber o = js_isNumber o
{-# INLINE isNumber #-}

isString :: JSVal -> Bool
isString o = js_isString o
{-# INLINE isString #-}

isBoolean :: JSVal -> Bool
isBoolean o = js_isBoolean o
{-# INLINE isBoolean #-}

isFunction :: JSVal -> Bool
isFunction o = js_isFunction o
{-# INLINE isFunction #-}

isSymbol :: JSVal -> Bool
isSymbol o = js_isSymbol o
{-# INLINE isSymbol #-}


{-
-- something that we can unsafeCoerce Text from
data Text' = Text'
    {-# UNPACK #-} !Array'           -- payload
    {-# UNPACK #-} !Int              -- offset
    {-# UNPACK #-} !Int              -- length

data Array' = Array' {
      aBA :: ByteArray#
    }

data Text'' = Text''
    {-# UNPACK #-} !Array''          -- payload
    {-# UNPACK #-} !Int              -- offset
    {-# UNPACK #-} !Int              -- length

data Array'' = Array'' {
      aRef :: Ref#
    }

-- same rep as Ptr Addr#, use this to get just the first field out
data Ptr' a = Ptr' ByteArray# Int#

ptrToPtr' :: Ptr a -> Ptr' b
ptrToPtr' = unsafeCoerce

ptr'ToPtr :: Ptr' a -> Ptr b
ptr'ToPtr = unsafeCoerce
-}
{-
toArray :: [JSVal a] -> IO (JSArray a)
toArray xs = Prim.toJSArray xs
{-# INLINE toArray #-}

pushArray :: JSVal a -> JSArray a -> IO ()
pushArray r arr = js_push r arr
{-# INLINE pushArray #-}

fromArray :: JSArray (JSVal a) -> IO [JSVal a]
fromArray a = Prim.fromJSArray a
{-# INLINE fromArray #-}

lengthArray :: JSArray a -> IO Int
lengthArray a = js_length a
{-# INLINE lengthArray #-}

indexArray :: Int -> JSArray a -> IO (JSVal a)
indexArray = js_index
{-# INLINE indexArray #-}

unsafeIndexArray :: Int -> JSArray a -> IO (JSVal a)
unsafeIndexArray = js_unsafeIndex
{-# INLINE unsafeIndexArray #-}

newArray :: IO (JSArray a)
newArray = js_emptyArray
{-# INLINE newArray #-}

newObj :: IO (JSVal a)
newObj = js_emptyObj
{-# INLINE newObj #-}

listProps :: JSVal a -> IO [JSString]
listProps o = fmap unsafeCoerce . Prim.fromJSArray =<< js_listProps o
{-# INLINE listProps #-}
-}
jsTypeOf :: JSVal -> JSType
jsTypeOf r = tagToEnum# (js_jsTypeOf r)
{-# INLINE jsTypeOf #-}

jsonTypeOf :: JSVal -> JSONType
jsonTypeOf r = tagToEnum# (js_jsonTypeOf r)
{-# INLINE jsonTypeOf #-}

{-
{- | Convert a JavaScript ArrayBuffer to a 'ByteArray' without copying. Throws
     a 'JSException' if the 'JSVal' is not an ArrayBuffer.
 -}
wrapBuffer :: Int          -- ^ offset from the start in bytes, if this is not a multiple of 8,
                           --   not all types can be read from the ByteArray#
           -> Int          -- ^ length in bytes (use zero or a negative number to use the whole ArrayBuffer)
           -> JSVal a      -- ^ JavaScript ArrayBuffer object
           -> IO ByteArray -- ^ result
wrapBuffer offset size buf = unsafeCoerce <$> js_wrapBuffer offset size buf
{-# INLINE wrapBuffer #-}

{- | Convert a JavaScript ArrayBuffer to a 'MutableByteArray' without copying. Throws
     a 'JSException' if the 'JSVal' is not an ArrayBuffer.
 -}
wrapMutableBuffer :: Int          -- ^ offset from the start in bytes, if this is not a multiple of 8,
                                  --   not all types can be read from / written to the ByteArray#
                  -> Int          -- ^ the length in bytes (use zero or a negative number to use the whole ArrayBuffer)
                  -> JSVal a      -- ^ JavaScript ArrayBuffer object
                  -> IO (MutableByteArray s)
wrapMutableBuffer offset size buf = unsafeCoerce <$> js_wrapBuffer offset size buf
{-# INLINE wrapMutableBuffer #-}

{- | Get the underlying JS object from a 'ByteArray#'. The object o
     contains an ArrayBuffer (o.buf) and several typed array views on it (which
     can have an offset from the start of the buffer and/or a reduced length):
      * o.i3 : 32 bit signed
      * o.u8 : 8  bit unsigned
      * o.u1 : 16 bit unsigned
      * o.f3 : 32 bit single precision float
      * o.f6 : 64 bit double precision float
      * o.dv : a DataView
    Some of the views will be null if the offset is not a multiple of 8.
 -}
byteArrayJSVal :: ByteArray# -> JSVal a
byteArrayJSVal a = unsafeCoerce (ByteArray a)
{-# INLINE byteArrayJSVal #-}

{- | Get the underlying JS object from a 'MutableByteArray#'. The object o
     contains an ArrayBuffer (o.buf) and several typed array views on it (which
     can have an offset from the start of the buffer and/or a reduced length):
      * o.i3 : 32 bit signed
      * o.u8 : 8  bit unsigned
      * o.u1 : 16 bit unsigned
      * o.f3 : 32 bit single precision float
      * o.f6 : 64 bit double precision float
      * o.dv : a DataView
    Some of the views will be null if the offset is not a multiple of 8.
 -}
mutableByteArrayJSVal :: MutableByteArray# s -> JSVal a
mutableByteArrayJSVal a = unsafeCoerce (MutableByteArray a)
{-# INLINE mutableByteArrayJSVal #-}

foreign import javascript safe "h$wrapBuffer($3, true, $1, $2)"
  js_wrapBuffer :: Int -> Int -> JSVal a -> IO (JSVal ())

{- | Convert an ArrayBuffer to a strict 'ByteString'
     this wraps the original buffer, without copying.
     Use 'byteArrayByteString' if you already have a wrapped buffer
 -}
bufferByteString :: Int        -- ^ offset from the start in bytes
                 -> Int        -- ^ length in bytes (use zero or a negative number to get the whole ArrayBuffer)
                 -> JSVal a
                 -> IO ByteString
bufferByteString offset length buf = do
  (ByteArray ba) <- wrapBuffer offset length buf
  byteArrayByteString ba

{- | Pack a ByteArray# primitive into a ByteString
     without copying the buffer.

     This is unsafe in native code
 -}
byteArrayByteString :: ByteArray#
                    -> IO ByteString
byteArrayByteString arr =
#ifdef ghcjs_HOST_OS
  let ba        = ByteArray arr
      !(Addr a) = byteArrayContents ba
  in  unsafePackAddressLen (sizeofByteArray ba) a
#else
  error "GHCJS.Foreign.byteArrayToByteString: not JS"
#endif

{- | Pack a MutableByteArray# primitive into a 'ByteString' without
     copying. The byte array shouldn't be modified after converting.

     This is unsafe in native code
 -}
unsafeMutableByteArrayByteString :: MutableByteArray# s
                                 -> IO ByteString
unsafeMutableByteArrayByteString arr =
#ifdef ghcjs_HOST_OS
  let ba        = MutableByteArray arr
      !(Addr a) = mutableByteArrayContents ba
  in  unsafePackAddressLen (sizeofMutableByteArray ba) a
#else
  error "GHCJS.Foreign.unsafeMutableByteArrayToByteString: no JS"
#endif
-}

-- -----------------------------------------------------------------------------

foreign import javascript unsafe
  "$r = $1===true;"
  js_fromBool :: JSVal -> Bool
foreign import javascript unsafe
  "$1 ? true : false"
  js_isTruthy :: JSVal -> Bool
foreign import javascript unsafe "$r = true;"  js_true :: Int# -> Ref#
foreign import javascript unsafe "$r = false;" js_false :: Int# -> Ref#
foreign import javascript unsafe "$r = null;"  js_null :: Int# -> Ref#
foreign import javascript unsafe "$r = undefined;"  js_undefined :: Int# -> Ref#
-- foreign import javascript unsafe "$r = [];" js_emptyArray :: IO (JSArray a)
-- foreign import javascript unsafe "$r = {};" js_emptyObj :: IO (JSVal a)
--foreign import javascript unsafe "$3[$1] = $2;"
--  js_unsafeWriteArray :: Int# -> JSVal a -> JSArray b -> IO ()
-- foreign import javascript unsafe "h$fromArray"
--  js_fromArray :: JSArray a -> IO Ref# -- [a]
--foreign import javascript safe "$2.push($1)"
--  js_push :: JSVal a -> JSArray a -> IO ()
--foreign import javascript safe "$1.length" js_length :: JSArray a -> IO Int
--foreign import javascript safe "$2[$1]"
--  js_index :: Int -> JSArray a -> IO (JSVal a)
--foreign import javascript unsafe "$2[$1]"
--  js_unsafeIndex :: Int -> JSArray a -> IO (JSVal a)
foreign import javascript unsafe "$2[$1]"
  js_unsafeGetProp :: JSString -> JSVal -> IO JSVal
foreign import javascript unsafe "$3[$1] = $2"
  js_unsafeSetProp :: JSString -> JSVal -> JSVal -> IO ()
{-
foreign import javascript safe "h$listProps($1)"
  js_listProps :: JSVal a -> IO (JSArray JSString)
-}
foreign import javascript unsafe "h$jsTypeOf($1)"
  js_jsTypeOf :: JSVal -> Int#
foreign import javascript unsafe "h$jsonTypeOf($1)"
  js_jsonTypeOf :: JSVal -> Int#
-- foreign import javascript unsafe "h$listToArray"
--  js_toArray :: Any -> IO (JSArray a)
-- foreign import javascript unsafe "$1 === null"
--  js_isNull      :: JSVal a -> Bool

-- foreign import javascript unsafe "h$isUndefined" js_isUndefined :: JSVal a -> Bool
foreign import javascript unsafe "h$isObject"    js_isObject    :: JSVal -> Bool
foreign import javascript unsafe "h$isBoolean"   js_isBoolean   :: JSVal -> Bool
foreign import javascript unsafe "h$isNumber"    js_isNumber    :: JSVal -> Bool
foreign import javascript unsafe "h$isString"    js_isString    :: JSVal -> Bool
foreign import javascript unsafe "h$isSymbol"    js_isSymbol    :: JSVal -> Bool
foreign import javascript unsafe "h$isFunction"  js_isFunction  :: JSVal -> Bool
