{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeOperators         #-}

module BuiltinFold where

import qualified PlutusTx.Builtins          as B
import qualified PlutusTx.Builtins.Internal as BI
import           PlutusTx.Prelude           as Plutus

import qualified Prelude                    as Haskell


{-# INLINABLE foldLeftScott #-}
foldLeftScott :: (b -> a -> b) -> b -> [a] -> b
foldLeftScott _ z []     = z
foldLeftScott f z (x:xs) = foldLeftScott f (f z x) xs

{-# INLINABLE sumLeftScott #-}
sumLeftScott :: [Integer] -> Integer
sumLeftScott l = foldLeftScott (+) 0 l

{-# INLINABLE foldRightScott #-}
foldRightScott :: (a -> b -> b) -> b -> [a] -> b
foldRightScott _ z []     = z
foldRightScott f z (x:xs) = f x Haskell.$! (foldRightScott f z xs)

{-# INLINABLE sumRightScott #-}
sumRightScott :: [Integer] -> Integer
sumRightScott l = foldRightScott (+) 0 l

---------------------------------------------------

{-# INLINABLE foldLeftBuiltin #-}
foldLeftBuiltin :: (b -> a -> b) -> b -> BI.BuiltinList a -> b
foldLeftBuiltin f z l = B.matchList l z (\x xs -> (foldLeftBuiltin f (f z x) xs))

{-# INLINABLE sumLeftBuiltin #-}
sumLeftBuiltin :: BI.BuiltinList Integer -> Integer
sumLeftBuiltin l = foldLeftBuiltin B.addInteger 0 l

{-# INLINABLE foldRightBuiltin #-}
foldRightBuiltin :: (a -> b -> b) -> b -> BI.BuiltinList a -> b
foldRightBuiltin f z l = B.matchList l z (\x xs -> f x Haskell.$! (foldRightBuiltin f z xs))

{-# INLINABLE sumRightBuiltin #-}
sumRightBuiltin :: BI.BuiltinList Integer -> Integer
sumRightBuiltin l = foldRightBuiltin B.addInteger 0 l
