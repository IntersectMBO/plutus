{-# LANGUAGE ForeignFunctionInterface, JavaScriptFFI,
             MagicHash, UnboxedTuples, UnliftedFFITypes, GHCForeignImportPrim
  #-}

{-
  Low level bindings for JavaScript strings. These expose the underlying
  encoding. Use Data.JSString for 
 -}
module Data.JSString.Raw ( rawHead
                         , rawTail
                         , rawInit
                         , rawLast
                         , rawLength
                         , rawTake
                         , rawDrop
                         , rawTakeEnd
                         , rawDropEnd
                         , rawChunksOf
                         , rawChunksOf'
                         ) where

import           GHC.Exts
  ( Int(..), Int#, Char(..)
  , negateInt#
  , (+#), (-#), (>=#), (<#)
  , isTrue#, chr#)
import qualified GHC.Exts as Exts
import GHCJS.Prim (JSVal)

import Unsafe.Coerce

import Data.JSString.Internal.Type


rawLength :: JSString -> Int
rawLength x = I# (js_length x)
{-# INLINE rawLength #-}

rawHead :: JSString -> Char
rawHead x
  | js_null x = emptyError "rawHead"
  | otherwise = C# (chr# (js_codePointAt 0# x))
{-# INLINE rawHead #-}

unsafeRawHead :: JSString -> Char
unsafeRawHead x = C# (chr# (js_codePointAt 0# x))
{-# INLINE unsafeRawHead #-}

rawLast :: JSString -> Char
rawLast x
  | js_null x = emptyError "rawLast"
  | otherwise = C# (chr# (js_charCodeAt (js_length x -# 1#) x))
{-# INLINE rawLast #-}

unsafeRawLast :: JSString -> Char
unsafeRawLast x = C# (chr# (js_charCodeAt (js_length x -# 1#) x))
{-# INLINE unsafeRawLast #-}

rawTail :: JSString -> JSString
rawTail x
  | js_null x = emptyError "rawTail"
  | otherwise = JSString $ js_tail x
{-# INLINE rawTail #-}

unsafeRawTail :: JSString -> JSString
unsafeRawTail x = JSString $ js_tail x
{-# INLINE unsafeRawTail #-}

rawInit :: JSString -> JSString
rawInit x = js_substr 0# (js_length x -# 1#) x
{-# INLINE rawInit #-}

unsafeRawInit :: JSString -> JSString
unsafeRawInit x = js_substr 0# (js_length x -# 1#) x
{-# INLINE unsafeRawInit #-}

unsafeRawIndex :: Int -> JSString -> Char
unsafeRawIndex (I# n) x = C# (chr# (js_charCodeAt n x))
{-# INLINE unsafeRawIndex #-}

rawIndex :: Int -> JSString -> Char
rawIndex (I# n) x
  | isTrue# (n <# 0#) || isTrue# (n >=# js_length x) =
      overflowError "rawIndex"
  | otherwise = C# (chr# (js_charCodeAt n x))
{-# INLINE rawIndex #-}
    
rawTake :: Int -> JSString -> JSString
rawTake (I# n) x = js_substr 0# n x
{-# INLINE rawTake #-}

rawDrop :: Int -> JSString -> JSString
rawDrop (I# n) x = js_substr1 n x
{-# INLINE rawDrop #-}

rawTakeEnd :: Int -> JSString -> JSString
rawTakeEnd (I# k) x = js_slice1 (negateInt# k) x
{-# INLINE rawTakeEnd #-}

rawDropEnd :: Int -> JSString -> JSString
rawDropEnd (I# k) x = js_substr 0# (js_length x -# k) x
{-# INLINE rawDropEnd #-}

rawChunksOf :: Int -> JSString -> [JSString]
rawChunksOf (I# k) x =
  let l     = js_length x
      go i = case i >=# l of
               0# -> js_substr i k x : go (i +# k)
               _  -> []
  in go 0#
{-# INLINE rawChunksOf #-}

rawChunksOf' :: Int -> JSString -> [JSString]
rawChunksOf' (I# k) x = unsafeCoerce (js_rawChunksOf k x)
{-# INLINE rawChunksOf' #-}

rawSplitAt :: Int -> JSString -> (JSString, JSString)
rawSplitAt (I# k) x = (js_substr 0# k x, js_substr1 k x)
{-# INLINE rawSplitAt #-}

emptyError :: String -> a
emptyError fun = error $ "Data.JSString.Raw." ++ fun ++ ": empty input"

overflowError :: String -> a
overflowError fun = error $ "Data.JSString.Raw." ++ fun ++ ": size overflow"

-- -----------------------------------------------------------------------------

foreign import javascript unsafe
  "$1===''" js_null :: JSString -> Bool
foreign import javascript unsafe
  "$1.length" js_length :: JSString -> Int#
foreign import javascript unsafe
  "$3.substr($1,$2)" js_substr :: Int# -> Int# -> JSString -> JSString
foreign import javascript unsafe
  "$2.substr($1)" js_substr1 :: Int# -> JSString -> JSString
foreign import javascript unsafe
  "$3.slice($1,$2)" js_slice :: Int# -> Int# -> JSString -> JSString
foreign import javascript unsafe
  "$2.slice($1)" js_slice1 :: Int# -> JSString -> JSString
foreign import javascript unsafe
  "$3.indexOf($1,$2)" js_indexOf :: JSString -> Int# -> JSString -> Int#
foreign import javascript unsafe
  "$2.indexOf($1)" js_indexOf1 :: JSString -> JSString -> Int#
foreign import javascript unsafe
  "$2.charCodeAt($1)" js_charCodeAt :: Int# -> JSString -> Int#
foreign import javascript unsafe
  "$2.codePointAt($1)" js_codePointAt :: Int# -> JSString -> Int#
foreign import javascript unsafe
  "$hsRawChunksOf" js_rawChunksOf :: Int# -> JSString -> Exts.Any -- [JSString]
foreign import javascript unsafe
  "h$jsstringTail" js_tail :: JSString -> JSVal -- null for empty string

