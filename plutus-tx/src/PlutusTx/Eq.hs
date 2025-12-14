{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module PlutusTx.Eq (Eq (..), (/=)) where

import PlutusTx.Bool
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Either (Either (..))
import Prelude (Maybe (..))

{- HLINT ignore -}

infix 4 ==, /=

-- Copied from the GHC definition

-- | The 'Eq' class defines equality ('==').
class Eq a where
  (==) :: a -> a -> Bool

-- (/=) deliberately omitted, to make this a one-method class which has a
-- simpler representation

(/=) :: Eq a => a -> a -> Bool
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

instance Eq a => Eq [a] where
  {-# INLINEABLE (==) #-}
  [] == [] = True
  (x : xs) == (y : ys) = x == y && xs == ys
  _ == _ = False

instance Eq Bool where
  {-# INLINEABLE (==) #-}
  True == True = True
  False == False = True
  _ == _ = False

instance Eq a => Eq (Maybe a) where
  {-# INLINEABLE (==) #-}
  (Just a1) == (Just a2) = a1 == a2
  Nothing == Nothing = True
  _ == _ = False

instance (Eq a, Eq b) => Eq (Either a b) where
  {-# INLINEABLE (==) #-}
  (Left a1) == (Left a2) = a1 == a2
  (Right b1) == (Right b2) = b1 == b2
  _ == _ = False

instance Eq () where
  {-# INLINEABLE (==) #-}
  _ == _ = True

instance (Eq a, Eq b) => Eq (a, b) where
  {-# INLINEABLE (==) #-}
  (a, b) == (a', b') = a == a' && b == b'
