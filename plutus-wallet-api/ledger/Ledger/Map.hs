{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
-- Prevent unboxing, which the plugin can't deal with
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
-- A map implementation that can be used in on-chain and off-chain code.
module Ledger.Map(
    Map
    , singleton
    , empty
    , fromList
    , toList
    , keys
    , lookup
    , union
    , all
    -- * These
    , These(..)
    , these
    ) where

import qualified Prelude                      as Haskell

import           Codec.Serialise.Class        (Serialise)
import           Data.Aeson                   (FromJSON (parseJSON), ToJSON (toJSON))
import           Data.Hashable                (Hashable)
import           Data.Swagger.Internal.Schema (ToSchema)
import           GHC.Generics                 (Generic)
import           Language.PlutusTx.Lift       (makeLift)
import           Language.PlutusTx.Prelude    hiding (all, lookup)
import qualified Language.PlutusTx.Prelude    as P

import           Ledger.These

{-# ANN module ("HLint: ignore Use newtype instead of data"::String) #-}

-- | A 'Map' of key-value pairs.
newtype Map k v = Map { unMap :: [(k, v)] }
    deriving (Show)
    deriving stock (Generic)
    deriving newtype (Eq, Ord)
    deriving anyclass (ToSchema, Serialise, Hashable)

instance Functor (Map k) where
    {-# INLINABLE fmap #-}
    fmap f (Map mp) =
        let
            go []           = []
            go ((c, i):xs') = (c, f i) : go xs'
        in Map (go mp)

-- This is the "better" instance for Maps that various people
-- have suggested, which merges conflicting entries with
-- the underlying semigroup for values.
instance (Eq k, Semigroup v) => Semigroup (Map k v) where
    (<>) = unionWith (<>)

instance (Eq k, Semigroup v) => Monoid (Map k v) where
    mempty = empty ()

instance (ToJSON v, ToJSON k) => ToJSON (Map k v) where
    toJSON = toJSON . unMap

instance (FromJSON v, FromJSON k) => FromJSON (Map k v) where
    parseJSON v = Map Haskell.<$> parseJSON v

{-# INLINABLE fromList #-}
fromList :: [(k, v)] -> Map k v
fromList = Map

{-# INLINABLE toList #-}
toList :: Map k v -> [(k, v)]
toList (Map l) = l

{-# INLINABLE lookup #-}
-- | Find an entry in a 'Map'.
lookup :: forall k v . (Eq k) => k -> Map k v -> Maybe v
lookup c (Map xs) =
    let
        go :: [(k, v)] -> Maybe v
        go []            = Nothing
        go ((c', i):xs') = if c' == c then Just i else go xs'
    in go xs

{-# INLINABLE keys #-}
-- | The keys of a 'Map'.
keys :: Map k v -> [k]
keys (Map xs) = P.fmap (\(k, _ :: v) -> k) xs

{-# INLINABLE union #-}
-- | Combine two 'Map's.
union :: forall k v r . (Eq k) => Map k v -> Map k r -> Map k (These v r)
union (Map ls) (Map rs) =
    let
        f :: v -> Maybe r -> These v r
        f a b' = case b' of
            Nothing -> This a
            Just b  -> These a b

        ls' :: [(k, These v r)]
        ls' = P.fmap (\(c, i) -> (c, f i (lookup c (Map rs)))) ls

        rs' :: [(k, r)]
        rs' = filter (\(c, _) -> not (any (\(c', _) -> c' == c) ls)) rs

        rs'' :: [(k, These v r)]
        rs'' = P.fmap (\(c, b) -> (c, That b)) rs'

    in Map (ls' ++ rs'')

{-# INLINABLE unionWith #-}
-- | Combine two 'Map's with the given combination function.
unionWith :: forall k a . (Eq k) => (a -> a -> a) -> Map k a -> Map k a -> Map k a
unionWith merge (Map ls) (Map rs) =
    let
        f :: a -> Maybe a -> a
        f a b' = case b' of
            Nothing -> a
            Just b  -> merge a b

        ls' :: [(k, a)]
        ls' = P.fmap (\(c, i) -> (c, f i (lookup c (Map rs)))) ls

        rs' :: [(k, a)]
        rs' = filter (\(c, _) -> not (any (\(c', _) -> c' == c) ls)) rs

    in Map (ls' ++ rs')

{-# INLINABLE all #-}
-- | See 'Data.Map.all'
all :: (v -> Bool) -> Map k v -> Bool
all p (Map mps) =
    let go xs = case xs of
            []              -> True
            (_ :: k, x):xs' -> p x && go xs'
    in go mps

{-# INLINABLE singleton #-}
-- | A singleton map.
singleton :: k -> v -> Map k v
singleton c i = Map [(c, i)]

-- This has to take unit otherwise it falls foul of the value restriction.
{-# INLINABLE empty #-}
-- | An empty 'Map'.
empty :: () -> Map k v
empty _ = Map ([] :: [(k, v)])

makeLift ''Map
