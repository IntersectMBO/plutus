-- Simplified Hashable, just to have something

module Data.Hashable(
  Hashable(..),
  ) where

--import Data.Bits
import Data.ByteString qualified as B
import Data.Complex
import Data.Fixed
import Data.Int
import Data.Integer (_integerToIntList)
import Data.List (foldl')
import Data.Ratio
import Data.Text qualified as T
import Data.Word

type Salt = Int

infixl 0 `hashWithSalt`

class Hashable a where
  hashWithSalt :: Salt -> a -> Int

  hash :: a -> Int
  hash = hashWithSalt defaultSalt

defaultSalt :: Salt
defaultSalt = 0x087fc72c

hashUsing :: (Hashable b) => (a -> b) -> Salt -> a -> Int
hashUsing f salt x = hashWithSalt salt (f x)

defaultHashWithSalt :: Hashable a => Int -> a -> Int
defaultHashWithSalt salt x = salt `hashInt` hash x

-----------------

instance Hashable Int where
    hash = id
    hashWithSalt = hashInt

instance Hashable Int8 where
    hash = fromIntegral
    hashWithSalt = defaultHashWithSalt

instance Hashable Int16 where
    hash = fromIntegral
    hashWithSalt = defaultHashWithSalt

instance Hashable Int32 where
    hash = fromIntegral
    hashWithSalt = defaultHashWithSalt

instance Hashable Int64 where
    hash = fromIntegral
    hashWithSalt = defaultHashWithSalt

instance Hashable Word where
    hash = fromIntegral
    hashWithSalt = defaultHashWithSalt

instance Hashable Word8 where
    hash = fromIntegral
    hashWithSalt = defaultHashWithSalt

instance Hashable Word16 where
    hash = fromIntegral
    hashWithSalt = defaultHashWithSalt

instance Hashable Word32 where
    hash = fromIntegral
    hashWithSalt = defaultHashWithSalt

instance Hashable Word64 where
    hash = fromIntegral
    hashWithSalt = defaultHashWithSalt

instance Hashable () where
    hash _ = 0
    hashWithSalt = defaultHashWithSalt

instance Hashable Bool where
    hash = fromEnum
    hashWithSalt = defaultHashWithSalt

instance Hashable Ordering where
    hash = fromEnum
    hashWithSalt = defaultHashWithSalt

instance Hashable Char where
    hash = fromEnum
    hashWithSalt = defaultHashWithSalt

instance Hashable Float where
  hash = hash . show
  hashWithSalt = defaultHashWithSalt

instance Hashable Double where
  hash = hash . show
  hashWithSalt = defaultHashWithSalt

instance Hashable Integer where
  hashWithSalt s = hashWithSalt s . _integerToIntList

instance Hashable B.ByteString where
  hashWithSalt s = hashWithSalt s . B.unpack

instance Hashable T.Text where
  hashWithSalt s = hashWithSalt s . T.unpack

distinguisher :: Int
distinguisher = fromIntegral $ (maxBound :: Word) `quot` 3

instance Hashable a => Hashable (Maybe a) where
    hash Nothing  = 0
    hash (Just a) = distinguisher `hashWithSalt` a
    hashWithSalt = defaultHashWithSalt

instance Hashable a => Hashable [a] where
    hashWithSalt = foldl' hashWithSalt

instance (Hashable a, Hashable b) => Hashable (Either a b) where
    hash (Left a)  = 0 `hashWithSalt` a
    hash (Right b) = distinguisher `hashWithSalt` b
    hashWithSalt = defaultHashWithSalt

instance Hashable a => Hashable (Complex a) where
  hashWithSalt s (r :+ i) = s `hashWithSalt` r `hashWithSalt` i

instance Hashable a => Hashable (Ratio a) where
  hashWithSalt s r = s `hashWithSalt` numerator r `hashWithSalt` denominator r

instance HasResolution a => Hashable (Fixed a) where
  hashWithSalt s = hashWithSalt s . toRational

instance (Hashable a1, Hashable a2) => Hashable (a1, a2) where
  hashWithSalt s (a1, a2) = s `hashWithSalt` a1 `hashWithSalt` a2

instance (Hashable a1, Hashable a2, Hashable a3) => Hashable (a1, a2, a3) where
  hashWithSalt s (a1, a2, a3) = s `hashWithSalt` a1 `hashWithSalt` a2 `hashWithSalt` a3

instance (Hashable a1, Hashable a2, Hashable a3, Hashable a4) => Hashable (a1, a2, a3, a4) where
  hashWithSalt s (a1, a2, a3, a4) = s `hashWithSalt` a1 `hashWithSalt` a2 `hashWithSalt` a3 `hashWithSalt` a4

------------

-- XXX This needs work
hashInt :: Salt -> Int -> Salt
hashInt s x = s * 33 + x

{-
-- This is what we'd like, but it uses primitives byteSwap# and timesWord2#

hashInt :: Salt -> Int -> Salt
hashInt s x = fromIntegral (mixHash (fromIntegral s) (fromIntegral x))

mulFold :: Word -> Word -> Word
mulFold (W# x) (W# y) = case timesWord2# x y of
    (# hi, lo #) -> W# (xor# hi lo)

byteSwap :: Word -> Word
byteSwap (W# w) = W# (byteSwap# w)

avalanche :: Word -> Word
avalanche z0 =
#if WORD_SIZE_IN_BITS == 64
   -- MurmurHash3Mixer
    let z1 = shiftXorMultiply 33 0xff51afd7ed558ccd z0
        z2 = shiftXorMultiply 33 0xc4ceb9fe1a85ec53 z1
        z3 = shiftXor 33 z2
    in z3
#else
   -- MurmurHash3Mixer 32bit
    let z1 = shiftXorMultiply 16 0x85ebca6b z0
        z2 = shiftXorMultiply 13 0xc2b2ae35 z1
        z3 = shiftXor 16 z2
    in z3
#endif

shiftXor :: Int -> Word -> Word
shiftXor n w = w `xor` (w `unsafeShiftR` n)

shiftXorMultiply :: Int -> Word -> Word -> Word
shiftXorMultiply n k w = shiftXor n w * k

-- | Mix hash is inspired by how xxh3 works on small (<=16byte) inputs.
mixHash :: Word -> Word -> Word
mixHash hi lo = avalanche (byteSwap lo + hi + mulFold hi lo)
-}
