{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE NoImplicitPrelude #-}

module PlutusBenchmark.Ed25519 (checkValid) where

import GHC.ByteOrder (ByteOrder (LittleEndian))
import PlutusBenchmark.SHA512 (sha512)
import PlutusTx.Prelude hiding (inv)

{-# INLINE checkValid #-}
checkValid ::
  BuiltinByteString ->
  BuiltinByteString ->
  BuiltinByteString ->
  Bool
checkValid sig message pubKey =
  let r = decodePoint (sliceByteString 0 32 sig)
      a = decodePoint pubKey
      s = decodeInt (sliceByteString 32 32 sig)
      hintArg = encodePoint r <> pubKey <> message
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
  | odd x /= x_0 = Point (q - x, yInt)
  | otherwise = Point (x, yInt)
  where
    x_0 = readBit bs 7
    x = xRecover yInt
    yInt = decodeInt $ clearBit 7 bs

encodePoint :: Point -> BuiltinByteString
encodePoint (Point (x, y)) = result
  where
    zeroPos :: Integer
    zeroPos = 7
    result = writeBits yBS [zeroPos] [xLSBVal]
    yBS = integerToByteString LittleEndian 32 y
    xBS = integerToByteString LittleEndian 32 x
    xLSBVal = readBit xBS 248

scalarMult :: Point -> Integer -> Point
scalarMult p e =
  if e == 0
    then Point (0, 1)
    else
      let q' = scalarMult p (e `divide` 2)
          q'' = edwards q' q'
       in if odd e then edwards q'' p else q''

edwards :: Point -> Point -> Point
edwards (Point (x1, y1)) (Point (x2, y2)) = Point (x3 `modulo` q, y3 `modulo` q)
  where
    x3 :: Integer
    x3 = (x1 * y2 + x2 * y1) * inv (1 + d * x1 * x2 * y1 * y2)
    y3 :: Integer
    y3 = (y1 * y2 + x1 * x2) * inv (1 - d * x1 * x2 * y1 * y2)

hint :: BuiltinByteString -> Integer
hint = byteStringToInteger LittleEndian . sha512

decodeInt :: BuiltinByteString -> Integer
decodeInt = byteStringToInteger LittleEndian

bx :: Integer
bx = xRecover by

by :: Integer
by = 4 * inv 5

-- 2 ^ 255 - 19, but as a constant
q :: Integer
q = 57896044618658097711785492504343953926634992332820282019728792003956564819949

xRecover :: Integer -> Integer
xRecover y =
  if
      | cond1 && not cond2 -> xA
      | cond1 && cond2     -> xAB
      | not cond1 && cond2 -> xB
      | otherwise          -> x
  where
    xx :: Integer
    xx = (y * y - 1) * inv (d * y * y + 1)
    x :: Integer
    x = expMod xx ((q + 3) `divide` 8) q
    xA :: Integer
    xA = x * i `modulo` q
    xB :: Integer
    xB = q - x
    xAB :: Integer
    xAB = q - xA
    cond1 :: Bool
    cond1 = (x * x - xx) `modulo` q /= 0 -- x here is always the input x
    cond2 :: Bool
    cond2 = if cond1 then odd xA else odd x

clearBit :: Integer -> BuiltinByteString -> BuiltinByteString
clearBit ix bs = writeBits bs [ix] [False]

inv :: Integer -> Integer
inv x = expMod x (q - 2) q

d :: Integer
d = (-121665) * inv 121666

expMod :: Integer -> Integer -> Integer -> Integer
expMod b' e m =
  if e == 0
    then 1
    else
      let reduced = expMod b' (e `divide` 2) m
          t = (reduced * reduced) `modulo` m
       in if odd e
            then (t * b') `modulo` m
            else t

i :: Integer
i = expMod 2 ((q - 1) `divide` 4) q
