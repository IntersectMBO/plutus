{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP          #-}

-- |Strict Decoder
module PlutusCore.Flat.Decoder.Strict
  ( decodeArrayWith
  , decodeListWith
  , dByteString
  , dLazyByteString
  , dShortByteString
  , dShortByteString_
#if! defined (ETA_VERSION)
  , dUTF16
#endif
  , dUTF8
  , dInteger
  , dNatural
  , dChar
  , dWord8
  , dWord16
  , dWord32
  , dWord64
  , dWord
  , dInt8
  , dInt16
  , dInt32
  , dInt64
  , dInt
  ) where

import Data.Bits
import Data.ByteString qualified as B
import Data.ByteString.Lazy qualified as L
import Data.ByteString.Short qualified as SBS
#if !MIN_VERSION_bytestring(0,11,0)
import Data.ByteString.Short.Internal qualified as SBS
#endif
import Control.Monad (unless)
import Data.DList qualified as DL
import Data.Int
import Data.Primitive.ByteArray
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import PlutusCore.Flat.Decoder.Prim
import PlutusCore.Flat.Decoder.Types

#if! defined (ETA_VERSION) && ! MIN_VERSION_text(2,0,0)
import Data.Text.Array qualified as TA
import Data.Text.Internal qualified as T
#endif

import Data.Word
import GHC.Base (unsafeChr)
import Numeric.Natural (Natural)
import PlutusCore.Flat.Data.ZigZag
#include "MachDeps.h"

decodeListWith :: Get a -> Get [a]
decodeListWith dec = do
  b <- dBool
  if b
    then Get $
         \end s -> do
           GetResult s' h <- runGet dec end s
           if s' /= s
             then
             let goNormal = do
                   b <- dBool
                   if b
                     then (:) <$> dec <*> goNormal
                     else pure []
                 {-# INLINE goNormal #-}
             in runGet ((h:) <$> goNormal) end s'
             else
             let goZero x =
                   let goZero'= do
                         b <- dBool
                         if b
                           then (x:) <$> goZero'
                           else pure []
                       {-# INLINE goZero' #-}
                   in goZero'
                 {-# INLINE goZero #-}
             in runGet ((h:) <$> goZero h) end s'
    else pure []
{-# INLINE decodeListWith #-}

decodeArrayWith :: Get a -> Get [a]
decodeArrayWith dec = DL.toList <$> getAsL_ dec

-- TODO: test if it would it be faster with DList.unfoldr :: (b -> Maybe (a, b)) -> b -> Data.DList.DList a
--  getAsL_ :: Flat a => Get (DL.DList a)
getAsL_ :: Get a -> Get (DL.DList a)
getAsL_ dec = do
  tag <- dWord8
  case tag of
    0 -> return DL.empty
    _ -> do
      h <- gets tag
      t <- getAsL_ dec
      return (DL.append h t)
  where
    gets 0 = return DL.empty
    gets n = DL.cons <$> dec <*> gets (n - 1)

{-# INLINE dNatural #-}
dNatural :: Get Natural
dNatural = dUnsigned

{-# INLINE dInteger #-}
dInteger :: Get Integer
dInteger = zagZig <$> dUnsigned

{-# INLINE dWord #-}
{-# INLINE dInt #-}
dWord :: Get Word
dInt :: Get Int

#if WORD_SIZE_IN_BITS == 64
dWord = (fromIntegral :: Word64 -> Word) <$> dWord64

dInt = (fromIntegral :: Int64 -> Int) <$> dInt64
#elif WORD_SIZE_IN_BITS == 32
dWord = (fromIntegral :: Word32 -> Word) <$> dWord32

dInt = (fromIntegral :: Int32 -> Int) <$> dInt32
#else
#error expected WORD_SIZE_IN_BITS to be 32 or 64
#endif








{-# INLINE dInt8 #-}
dInt8 :: Get Int8
dInt8 = zagZig <$> dWord8

{-# INLINE dInt16 #-}
dInt16 :: Get Int16
dInt16 = zagZig <$> dWord16

{-# INLINE dInt32 #-}
dInt32 :: Get Int32
dInt32 = zagZig <$> dWord32

{-# INLINE dInt64 #-}
dInt64 :: Get Int64
dInt64 = zagZig <$> dWord64

-- {-# INLINE dWord16  #-}
dWord16 :: Get Word16
dWord16 = wordStep 0 (wordStep 7 (lastStep 14)) 0

-- {-# INLINE dWord32  #-}
dWord32 :: Get Word32
dWord32 = wordStep 0 (wordStep 7 (wordStep 14 (wordStep 21 (lastStep 28)))) 0

-- {-# INLINE dWord64  #-}
dWord64 :: Get Word64
dWord64 =
  wordStep
    0
    (wordStep
       7
       (wordStep
          14
          (wordStep
             21
             (wordStep
                28
                (wordStep
                   35
                   (wordStep
                      42
                      (wordStep
                         49
                         (wordStep 56 (lastStep 63)))))))))
    0

{-# INLINE dChar #-}
dChar :: Get Char
-- dChar = chr . fromIntegral <$> dWord32
-- Not really faster than the simpler version above
dChar = charStep 0 (charStep 7 (lastCharStep 14)) 0

{-# INLINE charStep #-}
charStep :: Int -> (Int -> Get Char) -> Int -> Get Char
charStep !shl !cont !n = do
  !tw <- fromIntegral <$> dWord8
  let !w = tw .&. 127
  let !v = n .|. w `shift` shl
  if tw == w
    then return $ unsafeChr v
    else cont v

{-# INLINE lastCharStep #-}
lastCharStep :: Int -> Int -> Get Char
lastCharStep !shl !n = do
  !tw <- fromIntegral <$> dWord8
  let !w = tw .&. 127
  let !v = n .|. w `shift` shl
  if tw == w
    then if v > 0x10FFFF
           then charErr v
           else return $ unsafeChr v
    else charErr v
 where
  charErr v = fail $ "Unexpected extra byte or non unicode char" ++ show v

{-# INLINE wordStep #-}
wordStep :: (Bits a, Num a) => Int -> (a -> Get a) -> a -> Get a
wordStep shl k n = do
  tw <- fromIntegral <$> dWord8
  let w = tw .&. 127
  let v = n .|. w `shift` shl
  if tw == w
    then return v
    --else oneShot k v
    else k v

{-# INLINE lastStep #-}
lastStep :: (FiniteBits b, Show b, Num b) => Int -> b -> Get b
lastStep shl n = do
  tw <- fromIntegral <$> dWord8
  let w = tw .&. 127
  let v = n .|. w `shift` shl
  if tw == w
    then if countLeadingZeros w < shl
           then wordErr v
           else return v
    else wordErr v
 where
   wordErr v = fail $ "Unexpected extra byte in unsigned integer" ++ show v

-- {-# INLINE dUnsigned #-}
dUnsigned :: (Num b, Bits b) => Get b
dUnsigned = do
  (v, shl) <- dUnsigned_ 0 0
  maybe
    (return v)
    (\s ->
       if shl >= s
         then fail "Unexpected extra data in unsigned integer"
         else return v) $
    bitSizeMaybe v

-- {-# INLINE dUnsigned_ #-}
dUnsigned_ :: (Bits t, Num t) => Int -> t -> Get (t, Int)
dUnsigned_ shl n = do
  tw <- dWord8
  let w = tw .&. 127
  let v = n .|. fromIntegral w `shift` shl
  if tw == w
    then return (v, shl)
    else dUnsigned_ (shl + 7) v

--encode = encode . blob UTF8Encoding . L.fromStrict . T.encodeUtf8
--decode = T.decodeUtf8 . L.toStrict . (unblob :: BLOB UTF8Encoding -> L.ByteString) <$> decode

#if ! defined (ETA_VERSION)
-- BLOB UTF16Encoding
dUTF16 :: Get T.Text
dUTF16 = do
  _ <- dFiller
#if MIN_VERSION_text(2,0,0)
  -- Checked decoding (from UTF-8)
  T.decodeUtf16LE <$> dByteString_
#else
  -- Unchecked decoding (already UTF16)
  (ByteArray array, lengthInBytes) <- dByteArray_
  return (T.Text (TA.Array array) 0 (lengthInBytes `div` 2))
#endif
#endif

dUTF8 :: Get T.Text
dUTF8 = do
  _ <- dFiller
  bs <- dByteString_
  case T.decodeUtf8' bs of
    Right t -> pure t
    Left e  -> fail $ "Input contains invalid UTF-8 data" ++ show e

dFiller :: Get ()
dFiller = do
  tag <- dBool
  unless tag dFiller

dLazyByteString :: Get L.ByteString
dLazyByteString = dFiller >> dLazyByteString_

dShortByteString :: Get SBS.ShortByteString
dShortByteString = dFiller >> dShortByteString_

dShortByteString_ :: Get SBS.ShortByteString
dShortByteString_ = do
  (ByteArray array, _) <- dByteArray_
  return $ SBS.SBS array

dByteString :: Get B.ByteString
dByteString = dFiller >> dByteString_




