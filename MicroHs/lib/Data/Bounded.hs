module Data.Bounded(module Data.Bounded) where
import Prelude qualified ()
import Primitives

class Bounded a where
  minBound :: a
  maxBound :: a
