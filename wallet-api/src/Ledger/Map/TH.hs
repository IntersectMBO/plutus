{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MonoLocalBinds         #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -O0                 #-}
-- A map implementation that can be used in on-chain and off-chain code.
module Ledger.Map.TH(
    Map
    , IsEqual
    , singleton
    , empty
    , fromList
    , keys
    , map
    , lookup
    , union
    , all
    -- * These
    , These(..)
    , these
    ) where

import           Codec.Serialise.Class        (Serialise)
import           Data.Aeson                   (FromJSON(parseJSON), ToJSON(toJSON))
import           Data.Swagger.Internal.Schema (ToSchema)
import           GHC.Generics                 (Generic)
import           Language.PlutusTx.Lift       (makeLift)
import qualified Language.PlutusTx.Prelude    as P
import           Language.Haskell.TH          (Q, TExp)
import           Ledger.These.TH              (These(..), these)
import           Prelude                      hiding (all, lookup, map, negate)


-- | A 'Map' of key-value pairs. 
data Map k v = Map { unMap :: [(k, v)] }
    deriving (Show)
    deriving stock (Generic)
    deriving anyclass (ToSchema, Serialise)

makeLift ''Map

instance (ToJSON v, ToJSON k) => ToJSON (Map k v) where
    toJSON = toJSON . unMap

instance (FromJSON v, FromJSON k) => FromJSON (Map k v) where
    parseJSON v = Map <$> parseJSON v

fromList :: Q (TExp ([(k, v)] -> Map k v))
fromList = [|| Map ||]

-- | Apply a function to the values of a 'Map'.
map :: Q (TExp ((v -> w) -> Map k v -> Map k w))
map = [|| 
    let
        map :: forall k v w. (v -> w) -> Map k v -> Map k w
        map f (Map mp) =
            let 
                go :: [(k, v)] -> [(k, w)]
                go [] = []
                go ((c, i):xs') = (c, f i) : go xs'
            in Map (go mp)
    in
        map
    ||]

-- | Compare two 'k's for equality.
type IsEqual k = k -> k -> Bool

-- | Find an entry in a 'Map'.
lookup :: Q (TExp (IsEqual k -> k -> Map k v -> Maybe v))
lookup = [|| 

    let lookup :: forall k v. IsEqual k -> k -> Map k v -> Maybe v
        lookup eq c (Map xs) =
            let 
                go :: [(k, v)] -> Maybe v
                go []            = Nothing
                go ((c', i):xs') = if eq c' c then Just i else go xs'
            in go xs
    in
        lookup
 ||]

-- | The keys of a 'Map'.
keys :: Q (TExp (Map k v -> [k]))
keys = [|| 
    let keys' :: Map k v -> [k]
        keys' (Map xs) = $$(P.map) (\(k, _) -> k) xs
    in keys'
    ||]

-- | Combine two 'Map's.
union :: Q (TExp (IsEqual k -> Map k v -> Map k r -> Map k (These v r)))
union = [|| 

    let union :: forall k v r. IsEqual k -> Map k v -> Map k r -> Map k (These v r)
        union eq (Map ls) (Map rs) =
            let 
                f :: v -> Maybe r -> These v r
                f a b' = case b' of
                    Nothing -> This a
                    Just b  -> These a b

                ls' :: [(k, These v r)]
                ls' = $$(P.map) (\(c, i) -> (c, (f i ($$(lookup) eq c (Map rs))))) ls

                rs' :: [(k, r)]
                rs' = $$(P.filter) (\(c, _) -> $$(P.not) ($$(P.any) (\(c', _) -> eq c' c) ls)) rs

                rs'' :: [(k, These v r)]
                rs'' = $$(P.map) (\(c, b) -> (c, (That b))) rs'

            in Map ($$(P.append) ls' rs'')
    in union
    ||]

-- | See 'Data.Map.all'
all :: Q (TExp ((v -> Bool) -> Map k v -> Bool))
all = [|| 

    let all :: forall k v. (v -> Bool) -> Map k v -> Bool
        all p (Map mps) =
            let go xs = case xs of 
                    []         -> True
                    (_, x):xs' -> $$(P.and) (p x) (go xs')
            in go mps 
    in all ||]


-- | A singleton map.
singleton :: Q (TExp (k -> v -> Map k v))
singleton = [|| \c i -> Map [(c, i)] ||]

-- | An empty 'Map'.
empty :: Q (TExp (Map k v))
empty = [|| Map ([] :: [(k, v)]) ||]

    