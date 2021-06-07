{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE JavaScriptFFI #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}

{-
  experimental pure marshalling for lighter weight interaction in the quasiquoter
 -}
module GHCJS.Marshal.Pure ( PFromJSVal(..)
                          , PToJSVal(..)
                          ) where

import           Data.Char (chr, ord)
import           Data.Data
import           Data.Int (Int8, Int16, Int32)
import           Data.JSString.Internal.Type
import           Data.Maybe
import           Data.Text (Text)
import           Data.Typeable
import           Data.Word (Word8, Word16, Word32, Word)
import           Data.JSString
import           Data.JSString.Text
import           Data.Bits ((.&.))
import           Unsafe.Coerce (unsafeCoerce)
import           GHC.Int
import           GHC.Word
import           GHC.Types
import           GHC.Float
import           GHC.Prim

import           GHCJS.Types
import qualified GHCJS.Prim as Prim
import           GHCJS.Foreign.Internal
import           GHCJS.Marshal.Internal

{-
type family IsPureShared a where
  IsPureShared PureExclusive = False
  IsPureShared PureShared    = True

type family IsPureExclusive a where
  IsPureExclusive PureExclusive = True
  IsPureExclusive PureShared    = True
  -}

instance PFromJSVal JSVal where pFromJSVal = id
                                {-# INLINE pFromJSVal #-}
instance PFromJSVal ()    where pFromJSVal _ = ()
                                {-# INLINE pFromJSVal #-}

instance PFromJSVal JSString where pFromJSVal = JSString
                                   {-# INLINE pFromJSVal #-}
instance PFromJSVal [Char] where pFromJSVal   = Prim.fromJSString
                                 {-# INLINE pFromJSVal #-}
instance PFromJSVal Text   where pFromJSVal   = textFromJSVal
                                 {-# INLINE pFromJSVal #-}
instance PFromJSVal Char   where pFromJSVal x = C# (jsvalToChar x)
                                 {-# INLINE pFromJSVal #-}
instance PFromJSVal Bool   where pFromJSVal   = isTruthy
                                 {-# INLINE pFromJSVal #-}
instance PFromJSVal Int    where pFromJSVal x = I# (jsvalToInt x)
                                 {-# INLINE pFromJSVal #-}
instance PFromJSVal Int8   where pFromJSVal x = I8# (jsvalToInt8 x)
                                 {-# INLINE pFromJSVal #-}
instance PFromJSVal Int16  where pFromJSVal x = I16# (jsvalToInt16 x)
                                 {-# INLINE pFromJSVal #-}
instance PFromJSVal Int32  where pFromJSVal x = I32# (jsvalToInt x)
                                 {-# INLINE pFromJSVal #-}
instance PFromJSVal Word   where pFromJSVal x = W# (jsvalToWord x)
                                 {-# INLINE pFromJSVal #-}
instance PFromJSVal Word8  where pFromJSVal x = W8# (jsvalToWord8 x)
                                 {-# INLINE pFromJSVal #-}
instance PFromJSVal Word16 where pFromJSVal x = W16# (jsvalToWord16 x)
                                 {-# INLINE pFromJSVal #-}
instance PFromJSVal Word32 where pFromJSVal x = W32# (jsvalToWord x)
                                 {-# INLINE pFromJSVal #-}
instance PFromJSVal Float  where pFromJSVal x = F# (jsvalToFloat x)
                                 {-# INLINE pFromJSVal #-}
instance PFromJSVal Double where pFromJSVal x = D# (jsvalToDouble x)
                                 {-# INLINE pFromJSVal #-}

instance PFromJSVal a => PFromJSVal (Maybe a) where
    pFromJSVal x | isUndefined x || isNull x = Nothing
    pFromJSVal x = Just (pFromJSVal x)
    {-# INLINE pFromJSVal #-}

instance PToJSVal JSVal     where pToJSVal = id
                                  {-# INLINE pToJSVal #-}
instance PToJSVal JSString  where pToJSVal          = jsval
                                  {-# INLINE pToJSVal #-}
instance PToJSVal [Char]    where pToJSVal          = Prim.toJSString
                                  {-# INLINE pToJSVal #-}
instance PToJSVal Text      where pToJSVal          = jsval . textToJSString
                                  {-# INLINE pToJSVal #-}
instance PToJSVal Char      where pToJSVal (C# c)   = charToJSVal c
                                  {-# INLINE pToJSVal #-}
instance PToJSVal Bool      where pToJSVal True     = jsTrue
                                  pToJSVal False    = jsFalse
                                  {-# INLINE pToJSVal #-}
instance PToJSVal Int       where pToJSVal (I# x)   = intToJSVal x
                                  {-# INLINE pToJSVal #-}
instance PToJSVal Int8      where pToJSVal (I8# x)  = intToJSVal x
                                  {-# INLINE pToJSVal #-}
instance PToJSVal Int16     where pToJSVal (I16# x) = intToJSVal x
                                  {-# INLINE pToJSVal #-}
instance PToJSVal Int32     where pToJSVal (I32# x) = intToJSVal x
                                  {-# INLINE pToJSVal #-}
instance PToJSVal Word      where pToJSVal (W# x)   = wordToJSVal x
                                  {-# INLINE pToJSVal #-}
instance PToJSVal Word8     where pToJSVal (W8# x)  = wordToJSVal x
                                  {-# INLINE pToJSVal #-}
instance PToJSVal Word16    where pToJSVal (W16# x) = wordToJSVal x
                                  {-# INLINE pToJSVal #-}
instance PToJSVal Word32    where pToJSVal (W32# x) = wordToJSVal x
                                  {-# INLINE pToJSVal #-}
instance PToJSVal Float     where pToJSVal (F# x)   = floatToJSVal x
                                  {-# INLINE pToJSVal #-}
instance PToJSVal Double    where pToJSVal (D# x)   = doubleToJSVal x
                                  {-# INLINE pToJSVal #-}

instance PToJSVal a => PToJSVal (Maybe a) where
    pToJSVal Nothing  = jsNull
    pToJSVal (Just a) = pToJSVal a
    {-# INLINE pToJSVal #-}

foreign import javascript unsafe "$r = $1|0;"          jsvalToWord   :: JSVal -> Word#
foreign import javascript unsafe "$r = $1&0xff;"       jsvalToWord8  :: JSVal -> Word#
foreign import javascript unsafe "$r = $1&0xffff;"     jsvalToWord16 :: JSVal -> Word#
foreign import javascript unsafe "$r = $1|0;"          jsvalToInt    :: JSVal -> Int#
foreign import javascript unsafe "$r = $1<<24>>24;"    jsvalToInt8   :: JSVal -> Int#
foreign import javascript unsafe "$r = $1<<16>>16;"    jsvalToInt16  :: JSVal -> Int#
foreign import javascript unsafe "$r = +$1;"           jsvalToFloat  :: JSVal -> Float#
foreign import javascript unsafe "$r = +$1;"           jsvalToDouble :: JSVal -> Double#
foreign import javascript unsafe "$r = $1&0x7fffffff;" jsvalToChar   :: JSVal -> Char#

foreign import javascript unsafe "$r = $1;" wordToJSVal   :: Word#   -> JSVal
foreign import javascript unsafe "$r = $1;" intToJSVal    :: Int#    -> JSVal
foreign import javascript unsafe "$r = $1;" doubleToJSVal :: Double# -> JSVal
foreign import javascript unsafe "$r = $1;" floatToJSVal  :: Float#  -> JSVal
foreign import javascript unsafe "$r = $1;" charToJSVal   :: Char#   -> JSVal

