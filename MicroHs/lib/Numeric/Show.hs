module Numeric.Show(
  showSigned,
  showIntAtBase,
  showInt,
  showBin,
  showHex,
  showOct,
  showIntegral,
  ) where
import Control.Error
import Data.Bool
import Data.Char
import Data.Eq
import Data.Function
import Data.Integral
import Data.List
import Data.Num
import Data.Ord
import Prelude qualified ()
import Primitives
import Text.Show (ShowS, showChar)

showSigned :: forall a . (Ord a, Integral a) => (a -> ShowS) -> Int -> a -> ShowS
showSigned showPos p n r
    | n < 0 =
      if p > (6::Int) then
        '(' : '-' : showPos (-n) (')' : r)
      else
        '-' : showPos (-n) r
    | otherwise = showPos n r

-- | Shows a /non-negative/ 'Integral' number using the base specified by the
-- first argument, and the character representation specified by the second.
-- If the argument, n, is <0 and -n == n (i.e., n == minBound) it will
-- return the string for (abs n).
showIntAtBase :: forall a . (Ord a, Integral a) => a -> (Int -> Char) -> a -> ShowS
showIntAtBase base toChr an
  | base <= 1 = error "Numeric.showIntAtBase: unsupported base"
  | an < 0 =
    if -an < 0 then
      -- We are at minBound
      showPos (- quot an base) . showPos (- rem an base)
    else
      error "Numeric.showIntAtBase: negative argument"
  | otherwise = showPos an
   where
    showPos n r =
      let
        c = toChr (fromIntegral (rem n base))
      in  c `seq`
          if n < base then
            c : r
          else
            showPos (quot n base) (c : r)

showInt :: forall a . (Ord a, Integral a) => a -> ShowS
showInt = showIntAtBase 10 intToDigit

showHex :: forall a . (Ord a, Integral a) => a -> ShowS
showHex = showIntAtBase 16 intToDigit

showOct :: forall a . (Ord a, Integral a) => a -> ShowS
showOct = showIntAtBase 8  intToDigit

showBin :: forall a . (Ord a, Integral a) => a -> ShowS
showBin = showIntAtBase 2  intToDigit

showIntegral :: forall a . (Ord a, Integral a) => Int -> a -> ShowS
showIntegral = showSigned showInt
