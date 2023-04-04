{-# LANGUAGE TemplateHaskellQuotes #-}

{- | This module provides unfoldings for list methods that either don't have
 unfoldings, or whose unfoldings contain unsupported features.
-}
module PlutusTx.Compiler.Dictionary.List where

import Language.Haskell.TH qualified as TH
import Prelude hiding (Eq (..), Ord (..))
import Prelude qualified as Haskell

{-# INLINEABLE (==) #-}
(==) :: forall a. Haskell.Eq a => [a] -> [a] -> Bool
(==) [] []             = True
(==) (x : xs) (y : ys) = x Haskell.== y && xs == ys
(==) _ _               = False

{-# INLINEABLE (/=) #-}
(/=) :: forall a. Haskell.Eq a => [a] -> [a] -> Bool
(/=) xs ys = if xs == ys then False else True

selectorsEq :: [TH.Name]
selectorsEq =
    [ '(==)
    , '(/=)
    ]

{-# INLINEABLE compare #-}
compare :: forall a. Haskell.Ord a => [a] -> [a] -> Ordering
compare [] [] = EQ
compare [] (_ : _) = LT
compare (_ : _) [] = GT
compare (x : xs) (y : ys) = case Haskell.compare x y of
    EQ    -> compare xs ys
    other -> other

(<), (<=), (>), (>=) :: forall a. Haskell.Ord a => [a] -> [a] -> Bool
{-# INLINEABLE (<) #-}
(<) x y = case compare x y of LT -> True; _ -> False
{-# INLINEABLE (<=) #-}
(<=) x y = case compare x y of GT -> False; _ -> True
{-# INLINEABLE (>) #-}
(>) x y = case compare x y of GT -> True; _ -> False
{-# INLINEABLE (>=) #-}
(>=) x y = case compare x y of LT -> False; _ -> True

max, min :: forall a. Haskell.Ord a => [a] -> [a] -> [a]
max x y = if x <= y then y else x
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
