{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeOperators         #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module BuiltinFold where

import qualified PlutusTx.Builtins          as B
import qualified PlutusTx.Builtins.Internal as BI
import           PlutusTx.Prelude           as Plutus

import qualified Prelude                    as Haskell


{-# INLINABLE foldLeft #-}
foldLeft :: (b -> a -> b) -> b -> [a] -> b
foldLeft _ z []     = z
foldLeft f z (x:xs) = foldLeft f (f z x) xs

{-# INLINABLE sumLeft #-}
sumLeft :: [Integer] -> Integer
sumLeft l = foldLeft (+) 0 l

{-# INLINABLE foldRight #-}
foldRight :: (a -> b -> b) -> b -> [a] -> b
foldRight _ z []     = z
foldRight f z (x:xs) = f x Haskell.$! (foldRight f z xs)

{-# INLINABLE sumRight #-}
sumRight :: [Integer] -> Integer
sumRight l = foldRight (+) 0 l

---------------------------------------------------

{-# INLINABLE foldLeftX #-}
foldLeftX :: (b -> a -> b) -> b -> BI.BuiltinList a -> b
foldLeftX f z l = B.matchList l z (\x xs -> (foldLeftX f (f z x) xs))

{-# INLINABLE sumLeftX #-}
sumLeftX :: BI.BuiltinList Integer -> Integer
sumLeftX l = foldLeftX B.addInteger 0 l

{-# INLINABLE foldRightX #-}
foldRightX :: (a -> b -> b) -> b -> BI.BuiltinList a -> b
foldRightX f z l = B.matchList l z (\x xs -> f x Haskell.$! (foldRightX f z xs))

{-# INLINABLE sumRightX #-}
sumRightX :: BI.BuiltinList Integer -> Integer
sumRightX l = foldRightX B.addInteger 0 l
