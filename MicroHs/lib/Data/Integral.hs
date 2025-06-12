-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Integral(module Data.Integral) where
import Control.Error
import Data.Bool
import Data.Enum_Class
import Data.Eq
import Data.Integer_Type
import Data.Num
import Data.Ord
import Data.Real
import Prelude qualified ()
import Primitives

infixl 7 `quot`,`rem`
infixl 7 `div`,`mod`

-- XXX Importing Data.Enum causes an import cycle.
--     I don't really see the point of Enum as a superclass.
class (Real a, Enum a) => Integral a where
  quot      :: a -> a -> a
  rem       :: a -> a -> a
  div       :: a -> a -> a
  mod       :: a -> a -> a
  quotRem   :: a -> a -> (a, a)
  divMod    :: a -> a -> (a, a)
  toInteger :: a -> Integer

  n `quot` d       =  q  where (q,r) = quotRem n d
  n `rem` d        =  r  where (q,r) = quotRem n d
  n `div` d        =  q  where (q,r) = divMod n d
  n `mod` d        =  r  where (q,r) = divMod n d
  divMod n d       =  if signum r == negate (signum d) then (q - 1, r + d) else qr
                        where qr@(q,r) = quotRem n d
  quotRem n d      = (quot n d, rem n d)

gcd :: forall a . (Integral a) => a -> a -> a
gcd x y = gcd' (abs x) (abs y)
  where gcd' a b = if b == 0 then a else gcd' b (a `rem` b)

lcm :: forall a . (Integral a) => a -> a -> a
lcm x y =
  if x == 0 || y == 0 then
    0
  else
    abs ((x `quot` gcd x y) * y)

even :: forall a . (Integral a) => a -> Bool
even n = n `rem` 2 == 0

odd :: forall a . (Integral a) => a -> Bool
odd n = not (even n)

infixr 8 ^
(^) :: forall a b . (Num a, Integral b, Ord b) => a -> b -> a
x0 ^ y0 | y0 < 0    = error "Data.Integral.^: negative exponent"
        | otherwise = pow x0 y0
  -- This does not do the minimal number of multiplications, but it's simple.
  where pow x y | y == 0    = 1
                | even y    =     pow (x * x) (y `quot` 2)
                | otherwise = x * pow (x * x) (y `quot` 2)

fromIntegral :: forall a b . (Integral a, Num b) => a -> b
fromIntegral x = fromInteger (toInteger x)
