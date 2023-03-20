{-# LANGUAGE TemplateHaskellQuotes #-}

{- | This module provides unfoldings for Integer methods that either don't have
 unfoldings, or whose unfoldings contain unsupported features.
-}
module PlutusTx.Compiler.Dictionary.Integer where

import PlutusTx.Builtins qualified as Builtins

import Language.Haskell.TH qualified as TH
import Prelude hiding (Eq (..), Ord (..))

{-# INLINEABLE (==) #-}
(==) :: Integer -> Integer -> Bool
(==) = Builtins.equalsInteger

{-# INLINEABLE (/=) #-}
(/=) :: Integer -> Integer -> Bool
(/=) = Builtins.notEqualsInteger

selectorsEq :: [TH.Name]
selectorsEq =
    [ '(==)
    , '(/=)
    ]

{-# INLINEABLE compare #-}
compare :: Integer -> Integer -> Ordering
compare x y
    | x == y = EQ
    | x <= y = LT
    | otherwise = GT

(<), (<=), (>), (>=) :: Integer -> Integer -> Bool
{-# INLINEABLE (<) #-}
(<) = Builtins.lessThanInteger
{-# INLINEABLE (<=) #-}
(<=) = Builtins.lessThanEqualsInteger
{-# INLINEABLE (>) #-}
(>) = Builtins.greaterThanInteger
{-# INLINEABLE (>=) #-}
(>=) = Builtins.greaterThanEqualsInteger

max, min :: Integer -> Integer -> Integer
{-# INLINEABLE max #-}
max x y = if x <= y then y else x
{-# INLINEABLE min #-}
min x y = if x <= y then x else y

selectorsOrd :: [TH.Name]
selectorsOrd =
    [ 'compare
    , '(<)
    , '(<=)
    , '(>)
    , '(>=)
    , 'max
    , 'min
    ]
