-- copied & adapted from cryptic
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE GADTs               #-}
module Crypto.Math.Bits
    ( FBits(..)
    , FBitsK(..)
    , SizeValid
    , splitHalf
    , append
    , dropBitsOnRight
    , dropBitsOnLeft
    ) where

import Data.Bits
import Data.Proxy
import GHC.Natural
import GHC.TypeLits

-- | Finite Bits
--
-- Sadly Bits is taken by Bits operation
data FBits (n :: Nat) = FBits { unFBits :: Natural }
    deriving (Show,Eq,Ord)

data FBitsK = FBitsK (forall n . (KnownNat n, SizeValid n) => FBits n)

type SizeValid n = (KnownNat n, 1 <= n)

toFBits :: SizeValid n => Natural -> FBits n
toFBits nat = FBits nat .&. allOne

instance SizeValid n => Enum (FBits n) where
    toEnum i | i < 0 && fromIntegral i > unFBits maxi = error "FBits n not within bound"
             | otherwise                              = FBits (fromIntegral i)
      where maxi = allOne :: FBits n
    fromEnum (FBits n) = fromEnum n

instance SizeValid n => Bounded (FBits n) where
    minBound = FBits 0
    maxBound = allOne

instance SizeValid n => Num (FBits n) where
    fromInteger = toFBits . fromInteger
    (+) (FBits a) (FBits b) = toFBits (a + b)
    (-) (FBits a) (FBits b) = toFBits (a - b)
    (*) (FBits a) (FBits b) = toFBits (a * b)
    abs = id
    signum (FBits a)
        | a == 0    = FBits 0
        | otherwise = FBits 1

instance SizeValid n => Bits (FBits n) where
    (.&.) (FBits a) (FBits b) = FBits (a .&. b)
    (.|.) (FBits a) (FBits b) = FBits (a .|. b)
    xor (FBits a) (FBits b) = FBits (a `xor` b)
    shiftR (FBits a) n = FBits (a `shiftR` n)
    shiftL (FBits a) n = toFBits (a `shiftL` n) -- shiftL can overflow here, so explicit safe reconstruction from natural
    rotateL a i = ((a `shiftL` i) .|. (a `shiftR` (n - i)))
      where n = fromIntegral $ natVal (Proxy :: Proxy n)
    rotateR a i = ((a `shiftR` i) .|. (a `shiftL` (n - i)))
      where n = fromIntegral $ natVal (Proxy :: Proxy n)
    zeroBits = FBits 0
    bit i
        | i < 0 || fromIntegral i >= natVal (Proxy :: Proxy n) = FBits 0
        | otherwise                                            = FBits (2^i)
    testBit (FBits a) i = testBit a i
    bitSize _ = fromIntegral $ natVal (Proxy :: Proxy n)
    bitSizeMaybe _ = Just $ fromIntegral $ natVal (Proxy :: Proxy n)
    isSigned _ = False
    complement a = allOne `xor` a
    popCount (FBits a) = popCount a

allOne :: forall n . SizeValid n => FBits n
allOne = FBits (2 ^ n - 1)
  where n = natVal (Proxy :: Proxy n)

splitHalf :: forall m n . (SizeValid n, (n * 2) ~ m) => FBits m -> (FBits n, FBits n)
splitHalf (FBits a) = (FBits (a `shiftR` n), toFBits a)
  where n = fromIntegral $ natVal (Proxy :: Proxy n)

-- | Append 2 FBits together where the left member is shifted to make room for the right
-- element.
--
-- e.g. append (0x1 :: FBits 1) (0x70 :: FBits 7) = 0xf0 :: FBits 8
append :: forall m n r . (SizeValid m, SizeValid n, SizeValid r, (m + n) ~ r)
       => FBits n -> FBits m -> FBits r
append (FBits a) (FBits b) =
    FBits ((a `shiftL` m) .|.  b)
  where m = fromIntegral $ natVal (Proxy :: Proxy m)

--appendK :: FBitsK -> FBitsK -> FBitsK
--appendK (FBitsK a) (FBitsK b) = FBitsK (a `append` b)
    -- FBits ((a `shiftL` m) .|.  b)

dropBitsOnRight :: forall a b diff . (KnownNat diff, b <= a, SizeValid a, SizeValid b, (a - b) ~ diff)
              => FBits a
              -> FBits b
dropBitsOnRight (FBits a) = FBits (a `shiftR` fromInteger (natVal (Proxy :: Proxy diff)))

dropBitsOnLeft :: forall a b . (KnownNat b, b <= a, SizeValid a, SizeValid b)
             => FBits a
             -> FBits b
dropBitsOnLeft (FBits a) = toFBits a
