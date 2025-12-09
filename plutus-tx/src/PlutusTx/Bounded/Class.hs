module PlutusTx.Bounded.Class (Bounded (..)) where

class Bounded a where
  minBound :: a
  maxBound :: a
