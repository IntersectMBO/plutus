module PlutusCore.Crypto.BLS12_381.Bounds
  ( msmMaxScalarWords
  , msmScalarOutOfBounds
  ) where

{-|  The maximum size of a scalar for the BLS12-381 multiScalarMul functions.
64 words = 512 bytes = 4096 bits -}
msmMaxScalarWords :: Integer
msmMaxScalarWords = 64

msmMaxScalarBits :: Integer
msmMaxScalarBits = 64 * msmMaxScalarWords

msmScalarUb :: Integer
msmScalarUb = 2 ^ (msmMaxScalarBits - 1) - 1

msmScalarLb :: Integer
msmScalarLb = -(2 ^ (msmMaxScalarBits - 1))

msmScalarOutOfBounds :: Integer -> Bool
msmScalarOutOfBounds s = not (msmScalarLb <= s && s <= msmScalarUb)
{-# INLINE msmScalarOutOfBounds #-}
