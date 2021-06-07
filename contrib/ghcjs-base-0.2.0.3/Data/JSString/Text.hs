{-# LANGUAGE ForeignFunctionInterface, UnliftedFFITypes, JavaScriptFFI,
    UnboxedTuples, DeriveDataTypeable, GHCForeignImportPrim,
    MagicHash, FlexibleInstances, BangPatterns, Rank2Types, CPP #-}

{- | Conversion between 'Data.Text.Text' and 'Data.JSString.JSString'

 -}

module Data.JSString.Text
    ( textToJSString
    , textFromJSString
    , lazyTextToJSString
    , lazyTextFromJSString
    , textFromJSVal
    , lazyTextFromJSVal
    ) where

import GHCJS.Prim

import GHC.Exts (ByteArray#, Int(..), Int#, Any)

import Control.DeepSeq

import qualified Data.Text.Array as A
import qualified Data.Text as T
import qualified Data.Text.Internal as T
import qualified Data.Text.Lazy as TL

import Data.JSString.Internal.Type

import Unsafe.Coerce

textToJSString :: T.Text -> JSString
textToJSString (T.Text (A.Array ba) (I# offset) (I# length)) =
  js_toString ba offset length
{-# INLINE textToJSString #-}

textFromJSString :: JSString -> T.Text
textFromJSString j =
  case js_fromString j of
    (# _ , 0#     #) -> T.empty
    (# ba, length #) -> T.Text (A.Array ba) 0 (I# length)
{-# INLINE  textFromJSString #-}

lazyTextToJSString :: TL.Text -> JSString
lazyTextToJSString t = rnf t `seq` js_lazyTextToString (unsafeCoerce t)
{-# INLINE lazyTextToJSString #-}

lazyTextFromJSString :: JSString -> TL.Text
lazyTextFromJSString = TL.fromStrict . textFromJSString
{-# INLINE lazyTextFromJSString #-}

-- | returns the empty Text if not a string
textFromJSVal :: JSVal -> T.Text
textFromJSVal j = case js_fromString' j of
    (# _,  0#     #) -> T.empty
    (# ba, length #) -> T.Text (A.Array ba) 0 (I# length)
{-# INLINE textFromJSVal #-}

-- | returns the empty Text if not a string
lazyTextFromJSVal :: JSVal -> TL.Text
lazyTextFromJSVal = TL.fromStrict . textFromJSVal
{-# INLINE lazyTextFromJSVal #-}

-- ----------------------------------------------------------------------------

foreign import javascript unsafe
  "h$textToString($1,$2,$3)"
  js_toString :: ByteArray# -> Int# -> Int# -> JSString
foreign import javascript unsafe
  "h$textFromString"
  js_fromString :: JSString -> (# ByteArray#, Int# #)
foreign import javascript unsafe
  "h$textFromString"
  js_fromString' :: JSVal -> (# ByteArray#, Int# #)
foreign import javascript unsafe
  "h$lazyTextToString"
  js_lazyTextToString :: Any -> JSString
