{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
-- Prevent unboxing, which the plugin can't deal with
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
-- A map implementation that can be used in on-chain and off-chain code.
module Ledger.Map(
    Map
    , IsEqual
    , singleton
    , empty
    , fromList
    , toList
    , keys
    , map
    , lookup
    , union
    , all
    -- * These
    , These(..)
    , these
    ) where

import           Codec.Serialise.Class         (Serialise)
import           Data.Aeson                    (FromJSON (parseJSON), ToJSON (toJSON))
import           Data.Hashable                 (Hashable)
import           Data.Morpheus.Kind            (KIND, OBJECT, WRAPPER)
import           Data.Morpheus.Schema.TypeKind (TypeKind (OBJECT))
import           Data.Morpheus.Types           (Context (Context), DataField (fieldTypeWrappers), DataTypeWrapper (..),
                                                GQLType, InputType, Introspect (..), OutputType, updateLib)
import           Data.Proxy                    (Proxy (Proxy))
import           Data.Typeable                 (Typeable)
import           GHC.Generics                  (Generic)
import           Language.PlutusTx.Lift        (makeLift)
import           Language.PlutusTx.Prelude     hiding (all, lookup, map)
import qualified Language.PlutusTx.Prelude     as P

import           Ledger.These

{-# ANN module ("HLint: ignore Use newtype instead of data"::String) #-}

-- | A 'Map' of key-value pairs.
data Map k v = Map { unMap :: [(k, v)] }
    deriving (Show)
    deriving stock (Generic)
    deriving anyclass (Serialise, Hashable, GQLType)

makeLift ''Map

instance (ToJSON v, ToJSON k) => ToJSON (Map k v) where
    toJSON = toJSON . unMap

instance (FromJSON v, FromJSON k) => FromJSON (Map k v) where
    parseJSON v = Map <$> parseJSON v

{-# INLINABLE fromList #-}
fromList :: [(k, v)] -> Map k v
fromList = Map

{-# INLINABLE toList #-}
toList :: Map k v -> [(k, v)]
toList (Map l) = l

{-# INLINABLE map #-}
-- | Apply a function to the values of a 'Map'.
map :: forall k v w . (v -> w) -> Map k v -> Map k w
map f (Map mp) =
    let
        go :: [(k, v)] -> [(k, w)]
        go []           = []
        go ((c, i):xs') = (c, f i) : go xs'
    in Map (go mp)

-- | Compare two 'k's for equality.
type IsEqual k = k -> k -> Bool

{-# INLINABLE lookup #-}
-- | Find an entry in a 'Map'.
lookup :: forall k v . IsEqual k -> k -> Map k v -> Maybe v
lookup eq c (Map xs) =
    let
        go :: [(k, v)] -> Maybe v
        go []            = Nothing
        go ((c', i):xs') = if eq c' c then Just i else go xs'
    in go xs

{-# INLINABLE keys #-}
-- | The keys of a 'Map'.
keys :: Map k v -> [k]
keys (Map xs) = P.map (\(k, _ :: v) -> k) xs

{-# INLINABLE union #-}
-- | Combine two 'Map's.
union :: forall k v r . IsEqual k -> Map k v -> Map k r -> Map k (These v r)
union eq (Map ls) (Map rs) =
    let
        f :: v -> Maybe r -> These v r
        f a b' = case b' of
            Nothing -> This a
            Just b  -> These a b

        ls' :: [(k, These v r)]
        ls' = P.map (\(c, i) -> (c, f i (lookup eq c (Map rs)))) ls

        rs' :: [(k, r)]
        rs' = filter (\(c, _) -> not (any (\(c', _) -> eq c' c) ls)) rs

        rs'' :: [(k, These v r)]
        rs'' = P.map (\(c, b) -> (c, That b)) rs'

    in Map (ls' ++ rs'')

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


data Element k v = Element { key :: k, value :: v } deriving (Generic, GQLType)

type instance KIND (Element k v) = OBJECT

instance ( Introspect v (KIND v) f
         , Introspect v (KIND v) f
         , Introspect (Element k v) (KIND (Element k v)) f
         , Typeable k
         , Typeable v
         ) =>
         Introspect (Map k v) WRAPPER f where
  __field _ name =
    listField
      (__field
         (Context :: Context (Element k v) (KIND (Element k v)) f)
         name)
    where
      listField :: DataField f -> DataField f
      listField x =
        x {fieldTypeWrappers = [NonNullType, ListType] ++ fieldTypeWrappers x}
  introspect _ =
    introspect
      (Context :: Context (Element k v) (KIND (Element k v)) f)




    -- where
    --   (fields', stack') = unzip [ (("key", __field (Proxy :: Proxy k) "key"), introspect (Proxy :: Proxy k))
    --                             , (("value", __field (Proxy :: Proxy v) "value"), introspect (Proxy :: Proxy v))
    --                             ]
