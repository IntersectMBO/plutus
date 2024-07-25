{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE NoImplicitPrelude #-}

module PlutusBenchmark.Ed25519 (checkValid) where

import GHC.ByteOrder (ByteOrder (LittleEndian))
import PlutusBenchmark.SHA512 (sha512)
import PlutusTx.Prelude

{-# INLINE checkValid #-}
checkValid ::
  BuiltinByteString ->
  BuiltinByteString ->
  BuiltinByteString ->
  Bool
checkValid sig message pubkey =
  let sliced = sliceByteString 0 32 sig
      r = decodePoint sliced
      a = decodePoint pubkey
      s = byteStringToInteger LittleEndian (sliceByteString 32 32 sig)
      hintArg = encodePoint r <> pubkey <> message
      h = hint hintArg
    in scalarMult bPoint s == edwards r (scalarMult a h)

-- Helpers

newtype Point = Point (Integer, Integer)

instance Eq Point where
  Point (x1, y1) == Point (x2, y2) = x1 == x2 && y1 == y2

bPoint :: Point
bPoint = Point (bx `modulo` q, by `modulo` q)

decodePoint :: BuiltinByteString -> Point
decodePoint bs
  | odd x /= readBit bs 7 = Point (q - x, yInt)
  | otherwise = Point (x, yInt)
  where
    x :: Integer
    x = xRecover yInt
    yInt :: Integer
    yInt = byteStringToInteger LittleEndian . clearBit bs $ 7

encodePoint :: Point -> BuiltinByteString
encodePoint (Point (x, y)) = writeBits yBS [7] [readBit xBS 248]
  where
    yBS :: BuiltinByteString
    yBS = integerToByteString LittleEndian 32 y
    xBS :: BuiltinByteString
    xBS = integerToByteString LittleEndian 32 x

scalarMult :: Point -> Integer -> Point
scalarMult p e
  | e == 0 = Point (0, 1)
  | otherwise = let q' = scalarMult p (e `divide` 2)
                    q'' = edwards q' q'
                  in if odd e
                     then edwards q'' p
                     else q''

edwards :: Point -> Point -> Point
edwards (Point (x1, y1)) (Point (x2, y2)) =
  Point (x3 `modulo` q, y3 `modulo` q)
  where
    x3 :: Integer
    x3 = (x1 * y2 + x2 * y1) * inv' (1 + d * x1 * x2 * y1 * y2)
    y3 :: Integer
    y3 = (y1 * y2 + x1 * x2) * inv' (1 - d * x1 * x2 * y1 * y2)

-- So named because 'inv' is already taken by Group
inv' :: Integer -> Integer
inv' x = expMod x (q - 2) q

hint :: BuiltinByteString -> Integer
hint = byteStringToInteger LittleEndian . sha512

bx :: Integer
bx = xRecover by

-- 2 ^ 255 - 19, but as a constant
q :: Integer
q = 57896044618658097711785492504343953926634992332820282019728792003956564819949

by :: Integer
by = 4 * inv' 5

xRecover :: Integer -> Integer
xRecover y =
  if | cond1 && not cond2 -> xA
     | cond1 && cond2     -> xAB
     | not cond1 && cond2 -> xB
     | otherwise          -> x
  where
    cond1 :: Bool
    cond1 = (x * x - xx) `modulo` q /= 0
    cond2 :: Bool
    cond2 = if cond1 then odd xA else odd x
    xA :: Integer
    xA = x * i `modulo` q
    xAB :: Integer
    xAB = q - xA
    xB :: Integer
    xB = q - x
    x :: Integer
    x = expMod xx ((q + 3) `divide` 8) q
    xx :: Integer
    xx = (y * y - 1) * inv' (d * y * y + 1)

i :: Integer
i = expMod 2 ((q - 1) `divide` 4) q

clearBit :: BuiltinByteString -> Integer -> BuiltinByteString
clearBit bs ix = writeBits bs [ix] [False]

d :: Integer
d =  (-121665) * inv' 121666

expMod :: Integer -> Integer -> Integer -> Integer
expMod b e m
  | e == 0 = 1
  | otherwise = let reduced = expMod b (e `divide` 2) m
                    t = (reduced * reduced) `modulo` m
                  in if odd e
                     then (t * b) `modulo` m
                     else t
