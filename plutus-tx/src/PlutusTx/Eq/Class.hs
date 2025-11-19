module PlutusTx.Eq.Class
  ( Eq(..)
  , (/=)
  ) where

import PlutusTx.Bool
import PlutusTx.Builtins qualified as Builtins

{- HLINT ignore -}

infix 4 ==

-- Copied from the GHC definition

-- | The 'Eq' class defines equality ('==').
class Eq a where
  (==) :: a -> a -> Bool

-- (/=) deliberately omitted, to make this a one-method class which has a
-- simpler representation

infix 4 /=
(/=) :: (Eq a) => a -> a -> Bool
x /= y = not (x == y)
{-# INLINEABLE (/=) #-}

instance Eq Builtins.Integer where
  {-# INLINEABLE (==) #-}
  (==) = Builtins.equalsInteger

instance Eq Builtins.BuiltinByteString where
  {-# INLINEABLE (==) #-}
  (==) = Builtins.equalsByteString

instance Eq Builtins.BuiltinData where
  {-# INLINEABLE (==) #-}
  (==) = Builtins.equalsData

instance Eq Builtins.BuiltinString where
  {-# INLINEABLE (==) #-}
  (==) = Builtins.equalsString

instance Eq Builtins.BuiltinBLS12_381_G1_Element where
  {-# INLINEABLE (==) #-}
  (==) = Builtins.bls12_381_G1_equals

instance Eq Builtins.BuiltinBLS12_381_G2_Element where
  {-# INLINEABLE (==) #-}
  (==) = Builtins.bls12_381_G2_equals
