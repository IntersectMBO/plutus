-- copied & adapted from cryptic
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ViewPatterns        #-}
module Crypto.Math.Bytes
    ( Bytes
    , Endian(..)
    , pack
    , packSome
    , unpack
    , fromBits
    , toBits
    , append
    , take
    , drop
    , splitHalf
    , trace
    ) where

import           Data.Proxy
import           Data.Word
import           Data.List (foldl')
import           GHC.Natural
import           GHC.TypeLits
import           Crypto.Math.NatMath
import           Data.Bits (shiftL)
import           Crypto.Math.Bits (FBits(..))
import           Prelude hiding (take, drop)
import qualified Prelude
import qualified Debug.Trace as Trace

newtype Bytes (n :: Nat) = Bytes { unpack :: [Word8] }
    deriving (Show,Eq)

data Endian = LittleEndian | BigEndian
    deriving (Show,Eq)

pack :: forall n . KnownNat n => [Word8] -> Bytes n
pack l
    | n == len = Bytes l
    | otherwise = error "packing failed: length not as expected"
  where
    len = length l
    n = fromIntegral $ natVal (Proxy :: Proxy n)

packSome :: (forall n . KnownNat n => Bytes n -> a) -> [Word8] -> a
packSome f l = case someNatVal (fromIntegral len) of
                    Nothing          -> error "impossible"
                    Just (SomeNat (_ :: Proxy n)) -> f (pack l :: Bytes n)
  where len = length l

fixupBytes :: Endian -> [Word8] -> [Word8]
fixupBytes LittleEndian = reverse
fixupBytes BigEndian    = id

trace :: String -> Bytes n -> Bytes n
trace cmd b@(Bytes l) = Trace.trace (cmd ++ ": " ++ concatMap toHex l) b
  where
    toHex w = let (x,y) = w `divMod` 16 in [hex x, hex y]
    hex i | i < 10    = toEnum (fromEnum '0' + fromIntegral i)
          | otherwise = toEnum (fromEnum 'a' + fromIntegral (i-10))

-- | transform bytes into bits with a specific endianness
toBits :: Endian -> Bytes n -> FBits (n * 8)
toBits endian (Bytes l) = FBits $
    foldl' (\acc i -> (acc `shiftL` 8) + fromIntegral i) 0 (fixupBytes endian l)

-- | transform bits into bytes with a specific endianness
fromBits :: forall n . KnownNat n => Endian -> FBits n -> Bytes (Div8 n)
fromBits endian (unFBits -> allBits) = Bytes $ loop [] (0 :: Word) allBits
  where
    n = natVal (Proxy :: Proxy n)
    loop acc i nat
        | fromIntegral i > n  = error "binFromFBits over"
        | fromIntegral i == n = fixupBytes endian acc
        | otherwise           =
            let (nat', b) = divMod8 nat
             in loop (b:acc) (i+8) nat'

    divMod8 :: Natural -> (Natural, Word8)
    divMod8 i = let (q,m) = i `divMod` 256 in (q,fromIntegral m)


splitHalf :: forall m n . (KnownNat n, (n * 2) ~ m) => Bytes m -> (Bytes n, Bytes n)
splitHalf (Bytes l) = (Bytes l1, Bytes l2)
  where
    (l1, l2) = splitAt n l
    n = fromIntegral $ natVal (Proxy :: Proxy n)

append :: forall m n r . ((m + n) ~ r)
       => Bytes n -> Bytes m -> Bytes r
append (Bytes a) (Bytes b) = Bytes (a ++ b)

take :: forall n m .(KnownNat n, n <= m) => Bytes m -> Bytes n
take (Bytes l) = Bytes $ Prelude.take (fromIntegral $ natVal (Proxy :: Proxy n)) l

drop :: forall n m . (KnownNat m, KnownNat n, n <= m) => Bytes m -> Bytes n
drop (Bytes l) = Bytes $ Prelude.drop (fromIntegral diff) l
  where diff = natVal (Proxy :: Proxy m) - natVal (Proxy :: Proxy n)
