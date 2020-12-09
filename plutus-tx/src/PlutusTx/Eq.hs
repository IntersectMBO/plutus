{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Eq (Eq(..), (/=)) where

import           PlutusTx.Bool
import qualified PlutusTx.Builtins as Builtins
import           PlutusTx.Data

import           Prelude           hiding (Eq (..), not, (&&))

{-# ANN module ("HLint: ignore"::String) #-}

infix 4 ==, /=

-- Copied from the GHC definition
-- | The 'Eq' class defines equality ('==').
class Eq a where
    (==) :: a -> a -> Bool

    -- (/=) deliberately omitted, to make this a one-method class which has a
    -- simpler representation

{-# NOINLINE (/=) #-}
(/=) :: Eq a => a -> a -> Bool
x /= y = not (x == y)

instance Eq Integer where
    {-# NOINLINE (==) #-}
    (==) = Builtins.equalsInteger

instance Eq Builtins.ByteString where
    {-# NOINLINE (==) #-}
    (==) = Builtins.equalsByteString

instance Eq a => Eq [a] where
    {-# NOINLINE (==) #-}
    [] == []         = True
    (x:xs) == (y:ys) = x == y && xs == ys
    _ == _           = False

instance Eq Bool where
    {-# NOINLINE (==) #-}
    True == True   = True
    False == False = True
    _ == _         = False

instance Eq a => Eq (Maybe a) where
    {-# NOINLINE (==) #-}
    (Just a1) == (Just a2) = a1 == a2
    Nothing == Nothing     = True
    _ == _                 = False

instance (Eq a, Eq b) => Eq (Either a b) where
    {-# NOINLINE (==) #-}
    (Left a1) == (Left a2)   = a1 == a2
    (Right b1) == (Right b2) = b1 == b2
    _ == _                   = False

instance Eq () where
    {-# NOINLINE (==) #-}
    _ == _ = True

instance (Eq a, Eq b) => Eq (a, b) where
    {-# NOINLINE (==) #-}
    (a, b) == (a', b') = a == a' && b == b'

instance Eq Data where
    {-# NOINLINE (==) #-}
    Constr i ds == Constr i' ds' = i == i' && ds == ds'
    Constr _ _  == _             = False
    Map ds == Map ds'            = ds == ds'
    Map _  == _                  = False
    I i == I i'                  = i == i'
    I _ == _                     = False
    B b == B b'                  = b == b'
    B _ == _                     = False
    List ls == List ls'          = ls == ls'
    List _  == _                 = False
