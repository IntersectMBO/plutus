{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Enum (Enum(..)) where

import           PlutusTx.Builtins
import           Prelude           hiding (Enum (..))

class Enum a where
  succ :: a -> a
  pred :: a -> a
  toEnum :: Integer -> a
  fromEnum :: a -> Integer

instance Enum Integer where
  succ x = addInteger x 1
  pred x = subtractInteger x 1
  toEnum x = x
  fromEnum x = x
