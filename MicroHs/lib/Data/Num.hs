-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Num(module Data.Num) where
import Data.Integer_Type
import Prelude qualified ()
import Primitives

infixl 6 +,-
infixl 7 *

class Num a where
  (+) :: a -> a -> a
  (-) :: a -> a -> a
  (*) :: a -> a -> a
  negate :: a -> a
  abs :: a -> a
  signum :: a -> a
  fromInteger :: Integer -> a
  negate x = 0 - x

subtract :: forall a . Num a => a -> a -> a
subtract x y = y - x
