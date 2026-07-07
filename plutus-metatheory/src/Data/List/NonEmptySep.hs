{-# LANGUAGE DeriveAnyClass #-}

module Data.List.NonEmptySep
  ( NonEmptySep (..)
  , head
  , fromList
  ) where

import Control.DeepSeq
import GHC.Generics
import Prelude hiding (head)

-- | A non-empty list of `a`, separated by values of type `sep`
data NonEmptySep sep a
  = Cons a sep (NonEmptySep sep a)
  | Singleton a
  deriving (Show, Generic)
  deriving anyclass (NFData)

instance Functor (NonEmptySep sep) where
  fmap f (Singleton x) = Singleton (f x)
  fmap f (Cons x y xs) = Cons (f x) y (fmap f xs)

instance Foldable (NonEmptySep sep) where
  foldr f e (Singleton a) = f a e
  foldr f e (Cons x _ xs) = f x (foldr f e xs)

fromList :: ([(a, sep)], a) -> NonEmptySep sep a
fromList ([], x) = Singleton x
fromList ((x, y) : ys, z) = Cons x y (fromList (ys, z))

head :: NonEmptySep sep a -> a
head (Singleton x) = x
head (Cons x _ _) = x
