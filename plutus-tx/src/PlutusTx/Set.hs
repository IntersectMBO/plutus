{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -fno-omit-interface-pragmas
  -fno-strictness
  -fno-specialize #-}

module PlutusTx.Set
  ( Set
  , empty
  , singleton
  , insert
  , toList
  , fromList
  , null
  , member
  , size
  , all
  , delete
  , filter
  , map
  , union
  ) where

import           GHC.Generics          (Generic)
import qualified Prelude

import           Data.Aeson            (FromJSON (parseJSON), ToJSON)

import qualified PlutusTx              (makeLift)
import           PlutusTx.Builtins     (matchData, mkList, unsafeDataAsList)
import           PlutusTx.IsData.Class (FromData (fromBuiltinData), ToData (toBuiltinData),
                                        UnsafeFromData (unsafeFromBuiltinData))
import           PlutusTx.Prelude      hiding (all, filter, foldMap, map, null, toList)
import qualified PlutusTx.Prelude

-- | A collection of unique values.
newtype Set a = Set {unSet :: [a]}
  deriving stock (Prelude.Eq, Prelude.Show, Generic)
  deriving (Eq, Ord, ToJSON) via [a]

instance Ord a => Semigroup (Set a) where
  {-# INLINEABLE (<>) #-}
  (<>) = union

instance Ord a => Monoid (Set a) where
  {-# INLINEABLE mempty #-}
  mempty = empty

instance Foldable Set where
  {-# INLINEABLE foldMap #-}
  foldMap :: Monoid m => (a -> m) -> Set a -> m
  foldMap f = mconcat . fmap f . toList

instance (Ord a, FromJSON a) => FromJSON (Set a) where
  {-# INLINEABLE parseJSON #-}
  parseJSON = Prelude.fmap fromList . parseJSON

instance (ToData a) => ToData (Set a) where
  {-# INLINEABLE toBuiltinData #-}
  toBuiltinData (Set xs) = mkList . fmap toBuiltinData $ xs

instance (FromData a, Ord a) => FromData (Set a) where
  {-# INLINEABLE fromBuiltinData #-}
  fromBuiltinData dat =
    matchData
      dat
      (\_ -> const Nothing)
      (const Nothing)
      (foldrM go empty)
      (const Nothing)
      (const Nothing)
    where
      go :: BuiltinData -> Set a -> Maybe (Set a)
      go x acc = insert <$> fromBuiltinData x <*> pure acc

instance (UnsafeFromData a, Ord a) => UnsafeFromData (Set a) where
  {-# INLINEABLE unsafeFromBuiltinData #-}
  unsafeFromBuiltinData =
    foldr (insert . unsafeFromBuiltinData) empty . unsafeDataAsList

{-# INLINEABLE empty #-}
empty :: Set a
empty = Set []

{-# INLINEABLE singleton #-}
singleton :: a -> Set a
singleton x = Set [x]

{-# INLINEABLE insert #-}
insert :: forall a. Ord a => a -> Set a -> Set a
insert n = Set . go . unSet
  where
    go :: [a] -> [a]
    go [] = [n]
    go lst@(x : xs) = case compare n x of
      LT -> n : lst
      EQ -> lst
      GT -> x : go xs

{-# INLINEABLE toList #-}
toList :: Set a -> [a]
toList = unSet

{-# INLINEABLE fromList #-}
fromList :: Ord a => [a] -> Set a
fromList = foldr insert (Set [])

{-# INLINEABLE null #-}
null :: Set a -> Bool
null = PlutusTx.Prelude.null . unSet

{-# INLINEABLE member #-}
member :: forall a. Ord a => a -> Set a -> Bool
member n = go . unSet
  where
    go :: [a] -> Bool
    go [] = False
    go (x : xs) = case compare n x of
      LT -> False
      EQ -> True
      GT -> go xs

{-# INLINEABLE size #-}
size :: Set a -> Integer
size = length . toList

{-# INLINEABLE all #-}
all :: (a -> Bool) -> Set a -> Bool
all predicate = PlutusTx.Prelude.all predicate . toList

{-# INLINEABLE delete #-}
delete :: forall a. Ord a => a -> Set a -> Set a
delete n = Set . go . unSet
  where
    go :: [a] -> [a]
    go [] = []
    go lst@(x : xs) = case compare n x of
      LT -> lst
      EQ -> xs
      GT -> x : go xs

{-# INLINEABLE filter #-}
filter :: (a -> Bool) -> Set a -> Set a
filter f = Set . PlutusTx.Prelude.filter f . unSet

{- | The resulting set can be less than the initial size
if f maps two or more different keys to the same new key.
-}
{-# INLINEABLE map #-}
map :: Ord b => (a -> b) -> Set a -> Set b
map f = fromList . PlutusTx.Prelude.map f . unSet

{-# INLINEABLE union #-}
union :: Ord a => Set a -> Set a -> Set a
union x y = foldr insert x (toList y)

PlutusTx.makeLift ''Set
