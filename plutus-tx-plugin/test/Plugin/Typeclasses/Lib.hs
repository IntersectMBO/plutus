{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module Plugin.Typeclasses.Lib where

import PlutusTx.Builtins qualified as Builtins

data Animal = Dog | Cat
data Person = Jim | Jane
data Alien = AlienJim | AlienJane

-- Needs to be in another file because of #978
class DefaultMethods a where
  method1 :: a -> Integer
  {-# INLINEABLE method2 #-}
  method2 :: a -> Integer
  method2 a = method1 a `Builtins.addInteger` 1

instance DefaultMethods Integer where
  {-# INLINEABLE method1 #-}
  method1 a = a

instance DefaultMethods Person where
  {-# INLINEABLE method1 #-}
  method1 _ = 1
