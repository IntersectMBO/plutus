module Data.RealFrac(module Data.RealFrac) where
import qualified Prelude()
import Primitives
import Data.Ord
import Data.Fractional
import Data.Integral
import Data.Num
import Data.Real

class  (Ord a, Real a, Fractional a) => RealFrac a  where
  properFraction :: (Integral b) => a -> (b,a)
  truncate       :: (Integral b) => a -> b
  round          :: (Integral b) => a -> b
  ceiling        :: (Integral b) => a -> b
  floor          :: (Integral b) => a -> b

  truncate x     =  m  where (m,_) = properFraction x

  round x        =  let (n,r) = properFraction x
                        m     = if r < 0 then n - 1 else n + 1
                        s     = signum (abs r - 0.5)
                    in if s < 0 then n
                       else if s > 0 then m
                       else if even n then n else m

  ceiling x      =  if r > 0 then n + 1 else n
                      where (n,r) = properFraction x

  floor x        =  if r < 0 then n - 1 else n
                      where (n,r) = properFraction x
