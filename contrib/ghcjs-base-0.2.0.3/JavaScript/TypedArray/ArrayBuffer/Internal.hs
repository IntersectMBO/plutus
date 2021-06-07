{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE JavaScriptFFI #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}

module JavaScript.TypedArray.ArrayBuffer.Internal where

import GHCJS.Types

import GHCJS.Internal.Types
import GHCJS.Marshal.Pure

import GHC.Exts (State#)

import Data.Typeable

newtype SomeArrayBuffer (a :: MutabilityType s) =
  SomeArrayBuffer JSVal deriving Typeable
instance IsJSVal (SomeArrayBuffer m)

type ArrayBuffer           = SomeArrayBuffer Immutable
type MutableArrayBuffer    = SomeArrayBuffer Mutable
type STArrayBuffer s       = SomeArrayBuffer (STMutable s)

instance PToJSVal MutableArrayBuffer where
  pToJSVal (SomeArrayBuffer b) = b
instance PFromJSVal MutableArrayBuffer where
  pFromJSVal = SomeArrayBuffer

-- ----------------------------------------------------------------------------

foreign import javascript unsafe
  "$1.byteLength" js_byteLength :: SomeArrayBuffer any -> Int
foreign import javascript unsafe
  "new ArrayBuffer($1)" js_create :: Int -> State# s -> (# State# s, JSVal #)
foreign import javascript unsafe
  "$2.slice($1)" js_slice1 :: Int -> JSVal -> State# s -> (# State# s, JSVal #)

-- ----------------------------------------------------------------------------
-- immutable non-IO slice

foreign import javascript unsafe
  "$2.slice($1)" js_slice1_imm :: Int -> SomeArrayBuffer any -> SomeArrayBuffer any
foreign import javascript unsafe
  "$3.slice($1,$2)" js_slice_imm :: Int -> Int -> SomeArrayBuffer any -> SomeArrayBuffer any
