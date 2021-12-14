-- |
-- Module      : Foundation.Class.Storable
-- License     : BSD-style
-- Maintainer  : Haskell Foundation
-- Stability   : experimental
-- Portability : portable
--
-- <https://github.com/haskell-foundation/issues/111>
--
--

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP #-}

module Foundation.Class.Storable
    ( Storable(..)
    , StorableFixed(..)

      -- * Ptr
    , Ptr, plusPtr, castPtr
      -- * offset based helper
    , peekOff, pokeOff
      -- * Collection
    , peekArray
    , peekArrayEndedBy
    , pokeArray
    , pokeArrayEndedBy
    ) where

#include "MachDeps.h"

import GHC.Types (Double, Float)

import Foreign.Ptr (castPtr)
import qualified Foreign.Ptr
import qualified Foreign.Storable (peek, poke)

import Basement.Compat.Base
import Basement.Compat.C.Types (CChar, CUChar)
import Basement.Types.OffsetSize
import Basement.Types.Word128 (Word128(..))
import Basement.Types.Word256 (Word256(..))
import Foundation.Collection
import Foundation.Collection.Buildable (builderLift, build_)
import Basement.PrimType
import Basement.Endianness
import Foundation.Numerical

-- | Storable type of self determined size.
--
class Storable a where
    peek :: Ptr a -> IO a
    poke :: Ptr a -> a -> IO ()

-- | Extending the Storable type class to the types that can be sequenced
-- in a structure.
--
class Storable a => StorableFixed a where
    size :: proxy a -> CountOf Word8
    alignment :: proxy a -> CountOf Word8

plusPtr :: StorableFixed a => Ptr a -> CountOf a -> Ptr a
plusPtr ptr (CountOf num) = ptr `Foreign.Ptr.plusPtr` (num * (size ptr `align` alignment ptr))
  where
    align (CountOf sz) (CountOf a) = sz + (sz `mod` a)

-- | like `peek` but at a given offset.
peekOff :: StorableFixed a => Ptr a -> Offset a -> IO a
peekOff ptr off = peek (ptr `plusPtr` offsetAsSize off)

-- | like `poke` but at a given offset.
pokeOff :: StorableFixed a => Ptr a -> Offset a -> a -> IO ()
pokeOff ptr off = poke (ptr `plusPtr` offsetAsSize off)

peekArray :: (Buildable col, StorableFixed (Element col))
          => CountOf (Element col) -> Ptr (Element col) -> IO col
peekArray (CountOf s) p = build_ 64 . builder 0 $ p
  where
    builder off ptr
      | off == s = return ()
      | otherwise = do
          v <- builderLift (peekOff ptr (Offset off))
          append v
          builder (off + 1) ptr

peekArrayEndedBy :: (Buildable col, StorableFixed (Element col), Eq (Element col), Show (Element col))
                 => Element col -> Ptr (Element col) -> IO col
peekArrayEndedBy term p = build_ 64 . builder 0 $ p
  where
    builder off ptr = do
      v <- builderLift $ peekOff ptr off
      if term == v
        then return ()
        else append v >> builder (off + (Offset 1)) ptr

pokeArray :: (Sequential col, StorableFixed (Element col))
          => Ptr (Element col) -> col -> IO ()
pokeArray ptr arr =
    forM_ (z [0..] arr) $ \(i, e) ->
        pokeOff ptr (Offset i) e
  where
    z :: (Sequential col, Collection col) => [Int] -> col -> [(Int, Element col)]
    z = zip

pokeArrayEndedBy :: (Sequential col, StorableFixed (Element col))
                 => Element col -> Ptr (Element col) -> col -> IO ()
pokeArrayEndedBy term ptr col = do
    pokeArray ptr col
    pokeOff ptr (sizeAsOffset $ length col) term

instance Storable CChar where
    peek (Ptr addr) = primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0)
instance Storable CUChar where
    peek (Ptr addr) = primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0)
instance Storable Char where
    peek (Ptr addr) = primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0)
instance Storable Double where
    peek (Ptr addr) = primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0)
instance Storable Float where
    peek (Ptr addr) = primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0)
instance Storable Int8 where
    peek (Ptr addr) = primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0)
instance Storable Int16 where
    peek (Ptr addr) = primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0)
instance Storable Int32 where
    peek (Ptr addr) = primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0)
instance Storable Int64 where
    peek (Ptr addr) = primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0)
instance Storable Word8 where
    peek (Ptr addr) = primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0)
instance Storable Word16 where
    peek (Ptr addr) = primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0)
instance Storable (BE Word16) where
    peek (Ptr addr) = BE <$> primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0) . unBE
instance Storable (LE Word16) where
    peek (Ptr addr) = LE <$> primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0) . unLE
instance Storable Word32 where
    peek (Ptr addr) = primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0)
instance Storable (BE Word32) where
    peek (Ptr addr) = BE <$> primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0) . unBE
instance Storable (LE Word32) where
    peek (Ptr addr) = LE <$> primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0) . unLE
instance Storable Word64 where
    peek (Ptr addr) = primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0)
instance Storable (BE Word64) where
    peek (Ptr addr) = BE <$> primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0) . unBE
instance Storable (LE Word64) where
    peek (Ptr addr) = LE <$> primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0) . unLE
instance Storable Word128 where
    peek (Ptr addr) = primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0)
instance Storable (BE Word128) where
    peek (Ptr addr) = BE <$> primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0) . unBE
instance Storable (LE Word128) where
    peek (Ptr addr) = LE <$> primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0) . unLE
instance Storable Word256 where
    peek (Ptr addr) = primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0)
instance Storable (BE Word256) where
    peek (Ptr addr) = BE <$> primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0) . unBE
instance Storable (LE Word256) where
    peek (Ptr addr) = LE <$> primAddrRead addr (Offset 0)
    poke (Ptr addr) = primAddrWrite addr (Offset 0) . unLE
instance Storable (Ptr a) where
    peek = Foreign.Storable.peek
    poke = Foreign.Storable.poke

instance StorableFixed CChar where
    size      = const SIZEOF_CHAR
    alignment = const ALIGNMENT_CHAR
instance StorableFixed CUChar where
    size      = const SIZEOF_WORD8
    alignment = const ALIGNMENT_WORD8
instance StorableFixed Char where
    size      = const SIZEOF_HSCHAR
    alignment = const ALIGNMENT_HSCHAR
instance StorableFixed Double where
    size      = const SIZEOF_HSDOUBLE
    alignment = const ALIGNMENT_HSDOUBLE
instance StorableFixed Float where
    size      = const SIZEOF_HSFLOAT
    alignment = const ALIGNMENT_HSFLOAT
instance StorableFixed Int8 where
    size      = const SIZEOF_INT8
    alignment = const ALIGNMENT_INT8
instance StorableFixed Int16 where
    size      = const SIZEOF_INT16
    alignment = const ALIGNMENT_INT16
instance StorableFixed Int32 where
    size      = const SIZEOF_INT32
    alignment = const ALIGNMENT_INT32
instance StorableFixed Int64 where
    size      = const SIZEOF_INT64
    alignment = const ALIGNMENT_INT64
instance StorableFixed Word8 where
    size      = const SIZEOF_WORD8
    alignment = const ALIGNMENT_WORD8
instance StorableFixed Word16 where
    size      = const SIZEOF_WORD16
    alignment = const ALIGNMENT_WORD16
instance StorableFixed (BE Word16) where
    size      = const SIZEOF_WORD16
    alignment = const ALIGNMENT_WORD16
instance StorableFixed (LE Word16) where
    size      = const SIZEOF_WORD16
    alignment = const ALIGNMENT_WORD16
instance StorableFixed Word32 where
    size      = const SIZEOF_WORD32
    alignment = const ALIGNMENT_WORD32
instance StorableFixed (BE Word32) where
    size      = const SIZEOF_WORD32
    alignment = const ALIGNMENT_WORD32
instance StorableFixed (LE Word32) where
    size      = const SIZEOF_WORD32
    alignment = const ALIGNMENT_WORD32
instance StorableFixed Word64 where
    size      = const SIZEOF_WORD64
    alignment = const ALIGNMENT_WORD64
instance StorableFixed (BE Word64) where
    size      = const SIZEOF_WORD64
    alignment = const ALIGNMENT_WORD64
instance StorableFixed (LE Word64) where
    size      = const SIZEOF_WORD64
    alignment = const ALIGNMENT_WORD64
instance StorableFixed Word128 where
    size      = const 16
    alignment = const 16
instance StorableFixed (BE Word128) where
    size      = const 16
    alignment = const 16
instance StorableFixed (LE Word128) where
    size      = const 16
    alignment = const 16
instance StorableFixed Word256 where
    size      = const 32
    alignment = const 32
instance StorableFixed (BE Word256) where
    size      = const 32
    alignment = const 32
instance StorableFixed (LE Word256) where
    size      = const 32
    alignment = const 32
instance StorableFixed (Ptr a) where
    size      = const SIZEOF_HSPTR
    alignment = const ALIGNMENT_HSPTR
