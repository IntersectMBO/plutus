module Data.RealFloat(
  RealFloat(..),
  ) where
import Data.Bool
import Data.Eq
import Data.Floating
import Data.Fractional
import Data.Int
import Data.Integer
import Data.Num
import Data.Ord
import Prelude qualified ()
import Primitives

class (Fractional a, Ord a, Floating a) => RealFloat a  where
  floatRadix          :: a -> Integer
  floatDigits         :: a -> Int
  floatRange          :: a -> (Int,Int)
  decodeFloat         :: a -> (Integer,Int)
  encodeFloat         :: Integer -> Int -> a
  exponent            :: a -> Int
  significand         :: a -> a
  scaleFloat          :: Int -> a -> a
  isNaN               :: a -> Bool
  isInfinite          :: a -> Bool
  isDenormalized      :: a -> Bool
  isNegativeZero      :: a -> Bool
  isIEEE              :: a -> Bool
  atan2               :: a -> a -> a

  exponent x          =  if m == 0 then 0 else n + floatDigits x
                         where (m,n) = decodeFloat x

  significand x       =  encodeFloat m (- (floatDigits x))
                         where (m,_) = decodeFloat x

  scaleFloat 0 x      =  x
  scaleFloat k x
    | isFix           =  x
    | otherwise       =  encodeFloat m (n + clamp b k)
                         where (m,n) = decodeFloat x
                               (l,h) = floatRange x
                               d     = floatDigits x
                               b     = h - l + 4*d
                               -- n+k may overflow, which would lead
                               -- to wrong results, hence we clamp the
                               -- scaling parameter.
                               -- If n + k would be larger than h,
                               -- n + clamp b k must be too, similar
                               -- for smaller than l - d.
                               -- Add a little extra to keep clear
                               -- from the boundary cases.
                               isFix = x == 0 || isNaN x || isInfinite x

  atan2 y x
    | x > 0            =  atan (y/x)
    | x == 0 && y > 0  =  pi/2
    | x <  0 && y > 0  =  pi + atan (y/x)
    |(x <= 0 && y < 0)            ||
     (x <  0 && isNegativeZero y) ||
     (isNegativeZero x && isNegativeZero y)
                       = - (atan2 (- y) x)
    | y == 0 && (x < 0 || isNegativeZero x)
                        =  pi    -- must be after the previous test on zero y
    | x==0 && y==0      =  y     -- must be after the other double zero tests
    | otherwise         =  x + y -- x or y is a NaN, return a NaN (via +)

clamp :: Int -> Int -> Int
clamp bd k = max (- bd) (min bd k)
