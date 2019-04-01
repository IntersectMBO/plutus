{-# LANGUAGE TemplateHaskell #-}

-- A map implementation that can be used in on-chain and off-chain code.
module Ledger.Map(
    Map
    , IsEqual
    , singleton
    , empty
    , map
    , lookup
    , union
    , all
    -- * These
    , These(..)
    , these
    ) where
    
import           Ledger.Map.TH (IsEqual, Map, These(..))
import qualified Ledger.Map.TH as TH
import           Prelude hiding (all, lookup, map)

-- | See 'Ledger.Map.TH.map'
map :: (v -> w) -> Map k v -> Map k w
map = $$(TH.map)

-- | See 'Ledger.Map.TH.lookup'
lookup :: IsEqual k -> k -> Map k v -> Maybe v
lookup = $$(TH.lookup)

-- | See 'Ledger.Map.TH.union'
union :: IsEqual k -> Map k v -> Map k r -> Map k (These v r)
union = $$(TH.union)

-- | See 'Ledger.Map.TH.all'
all :: (v -> Bool) -> Map k v -> Bool
all = $$(TH.all)

-- | See 'Ledger.Map.TH.singleton'
singleton :: k -> v -> Map k v
singleton = $$(TH.singleton)

-- | See 'Ledger.Map.TH.empty'
empty :: Map k v
empty = $$(TH.empty)

-- | See 'Ledger.These.TH.these'
these :: (a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c
these = $$(TH.these)
