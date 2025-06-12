module Data.Floating(module Data.Floating) where
import Data.Fractional
import Data.Num
import Prelude qualified ()
import Primitives

infixr 8 **

class (Fractional a) => Floating a  where
  pi       :: a
  exp      :: a -> a
  log      :: a -> a
  sqrt     :: a -> a
  (**)     :: a -> a -> a
  logBase  :: a -> a -> a
  sin      :: a -> a
  cos      :: a -> a
  tan      :: a -> a
  asin     :: a -> a
  acos     :: a -> a
  atan     :: a -> a
  sinh     :: a -> a
  cosh     :: a -> a
  tanh     :: a -> a
  asinh    :: a -> a
  acosh    :: a -> a
  atanh    :: a -> a
  log1p    :: a -> a
  expm1    :: a -> a
  log1pexp :: a -> a
  log1mexp :: a -> a

  x ** y              = exp (log x * y)
  logBase x y         = log y / log x
  sqrt x              = x ** (1/2)
  tan  x              = sin  x / cos  x
  sinh x              = (exp x - exp (- x)) / 2
  cosh x              = (exp x + exp (- x)) / 2
  tanh x              = sinh x / cosh x
  asinh x             = log (x + sqrt (x*x + 1))
  acosh x             = log (x + sqrt (x*x - 1))
  atanh x             = log ((x + 1) / (x - 1)) / 2
  log1p x             = log (1 + x)
  expm1 x             = exp x - 1
  log1pexp x          = log1p (exp x)
  log1mexp x          = log1p (- (exp x))
