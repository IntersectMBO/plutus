-- |
-- Module      : Foundation.Hashing.Hashable
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : good
--
-- provide the SipHash algorithm.
-- reference: <http://131002.net/siphash/siphash.pdf>
--
module Foundation.Hashing.Hashable
    ( Hashable(..)
    ) where

import           Basement.Imports
import           Basement.Cast (cast)
import           Basement.Compat.Natural
import           Basement.Types.Word128
import           Basement.Types.Word256
import           Basement.IntegralConv
import           Basement.Numerical.Multiplicative
import qualified Basement.BoxedArray as A
import           Foundation.Tuple
import           Foundation.String
import           Foundation.Collection.Foldable
import           Foundation.Hashing.Hasher

-- | Type with the ability to be hashed
--
-- Hashable doesn't have any specific rules, and it's
-- made for raw speed. More specifically don't expect different
-- type representing the same data to hash to the same value
--
-- > hashMix (1 :: Integer) /= hashMix (1 :: Word8)
-- True
class Hashable a where
    hashMix :: Hasher st => a -> st -> st

-- specific type instances
instance Hashable Word8 where
    hashMix w = hashMix8 w
instance Hashable Word16 where
    hashMix w = hashMix16 w
instance Hashable Word32 where
    hashMix w = hashMix32 w
instance Hashable Word64 where
    hashMix w = hashMix64 w
instance Hashable Word128 where
    hashMix (Word128 w1 w2) = hashMix64 w2 . hashMix64 w1
instance Hashable Word256 where
    hashMix (Word256 w1 w2 w3 w4) = hashMix64 w4 . hashMix64 w3 . hashMix64 w2 . hashMix64 w1
instance Hashable Natural where
    hashMix n iacc
        | n == 0    = hashMix8 0 iacc
        | otherwise = loop n iacc
      where
        loop 0 acc = acc
        loop w acc =
            let b = integralDownsize (w :: Natural) :: Word8
             in loop (w `div` 256) (hashMix8 b acc)
instance Hashable Int8 where
    hashMix w = hashMix8 (cast w)
instance Hashable Int16 where
    hashMix w = hashMix16 (cast w)
instance Hashable Int32 where
    hashMix w = hashMix32 (cast w)
instance Hashable Int64 where
    hashMix w = hashMix64 (cast w)
instance Hashable Integer where
    hashMix i iacc
        | i == 0    = hashMix8 0 iacc
        | i < 0     = loop (integerToNatural i) (hashMix8 1 iacc)
        | otherwise = loop (integerToNatural i) (hashMix8 0 iacc)
      where
        loop :: Hasher st => Natural -> st -> st
        loop 0 acc = acc
        loop w acc =
            let b = integralDownsize w :: Word8
             in loop (w `div` 256) (hashMix8 b acc)

instance Hashable String where
    hashMix s = hashMixBytes (toBytes UTF8 s)

-- collection type instances
instance PrimType a => Hashable (UArray a) where
    hashMix ba = hashMixBytes ba
instance Hashable a => Hashable (A.Array a) where
    hashMix arr st = A.foldl' (flip hashMix) st arr

-- combined instances
instance Hashable a => Hashable [a] where
    hashMix ba st = foldl' (flip hashMix) st ba

instance (Hashable a, Hashable b) => Hashable (a,b) where
    hashMix (a,b) = hashMix b . hashMix a
instance (Hashable a, Hashable b, Hashable c) => Hashable (a,b,c) where
    hashMix (a,b,c) = hashMix c . hashMix b . hashMix a
instance (Hashable a, Hashable b, Hashable c, Hashable d) => Hashable (a,b,c,d) where
    hashMix (a,b,c,d) = hashMix d . hashMix c . hashMix b . hashMix a
instance (Hashable a, Hashable b, Hashable c, Hashable d, Hashable e) => Hashable (a,b,c,d,e) where
    hashMix (a,b,c,d,e) = hashMix e . hashMix d . hashMix c . hashMix b . hashMix a
instance (Hashable a, Hashable b, Hashable c, Hashable d, Hashable e, Hashable f) => Hashable (a,b,c,d,e,f) where
    hashMix (a,b,c,d,e,f) = hashMix f . hashMix e . hashMix d . hashMix c . hashMix b . hashMix a
instance (Hashable a, Hashable b) => Hashable (Tuple2 a b) where
    hashMix (Tuple2 a b) = hashMix b . hashMix a
instance (Hashable a, Hashable b, Hashable c) => Hashable (Tuple3 a b c) where
    hashMix (Tuple3 a b c) = hashMix c . hashMix b . hashMix a
instance (Hashable a, Hashable b, Hashable c, Hashable d) => Hashable (Tuple4 a b c d) where
    hashMix (Tuple4 a b c d) = hashMix d . hashMix c . hashMix b . hashMix a
{-
instance (Hashable a, Hashable b, Hashable c, Hashable d, Hashable e) => Hashable (Tuple5 a b c d e) where
    hashMix (Tuple5 a b c d e) = hashMix e . hashMix d . hashMix c . hashMix b . hashMix a
instance (Hashable a, Hashable b, Hashable c, Hashable d, Hashable e, Hashable f) => Hashable (Tuple6 a b c d e f) where
    hashMix (Tuple6 a b c d e f) = hashMix f . hashMix e . hashMix d . hashMix c . hashMix b . hashMix a
-}
