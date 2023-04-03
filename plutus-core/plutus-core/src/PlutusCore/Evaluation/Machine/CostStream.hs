{-# LANGUAGE BangPatterns #-}

module PlutusCore.Evaluation.Machine.CostStream
    ( CostStream(..)
    , unconsCost
    , reconsCost
    , sumCostStream
    , mapCostStream
    , addCostStream
    , minCostStream
    ) where

import PlutusCore.Evaluation.Machine.ExMemory

-- | A lazy stream of 'CostingInteger's. Basically @NonEmpty CostingInteger@, except the elements
-- are stored strictly.
--
-- The semantics of a stream are those of the sum of its elements. I.e. a stream that is a reordered
-- version of another stream is considered equal to that stream.
data CostStream
    = CostLast {-# UNPACK #-} !CostingInteger
    | CostCons {-# UNPACK #-} !CostingInteger CostStream
    deriving stock (Show)

-- TODO: (# CostingInteger, (# (# #) | CostStream #) #)?
-- | Uncons an element from a 'CostStream' and return the rest of the stream, if not empty.
unconsCost :: CostStream -> (CostingInteger, Maybe CostStream)
unconsCost (CostLast cost)       = (cost, Nothing)
unconsCost (CostCons cost costs) = (cost, Just costs)
{-# INLINE unconsCost #-}

-- | Cons an element to a 'CostStream', if given any. Otherwise create a new 'CostStream' using
-- 'CostLast'.
reconsCost :: CostingInteger -> Maybe CostStream -> CostStream
reconsCost cost = maybe (CostLast cost) (CostCons cost)
{-# INLINE reconsCost #-}

{- Note [Global local functions]
Normally when defining a helper function one would put it into a @where@ or a @let@ block.
However if the enclosing function gets inlined, then the definition of the helper one gets inlined
too, which when happens in multiple places can create serious GHC Core bloat, making it really hard
to analyze the generated code. Hence in some cases we optimize for lower amounts of produced GHC
Core by turning some helper functions into global ones.

This doesn't work as well when the helper function captures a variables bound by the enclosing one,
so we leave such helper functions local. We could probably create a global helper and a local
function within it instead, but so far it doesn't appear as those capturing helpers actually get
duplicated in the generated Core.
-}

-- See Note [Global local functions].
sumCostStreamGo :: CostingInteger -> CostStream -> CostingInteger
sumCostStreamGo !acc (CostLast cost)       = acc + cost
sumCostStreamGo !acc (CostCons cost costs) = sumCostStreamGo (acc + cost) costs

-- | Add up all the costs in a 'CostStream'.
sumCostStream :: CostStream -> CostingInteger
sumCostStream (CostLast cost0)        = cost0
sumCostStream (CostCons cost0 costs0) = sumCostStreamGo cost0 costs0
{-# INLINE sumCostStream #-}

-- See Note [Global local functions].
-- | Map a function over a 'CostStream'.
mapCostStream :: (CostingInteger -> CostingInteger) -> CostStream -> CostStream
mapCostStream f (CostLast cost0)        = CostLast (f cost0)
mapCostStream f (CostCons cost0 costs0) = CostCons (f cost0) $ go costs0 where
    go :: CostStream -> CostStream
    go (CostLast cost)       = CostLast (f cost)
    go (CostCons cost costs) = CostCons (f cost) $ go costs
{-# INLINE mapCostStream #-}

-- See Note [Global local functions].
addCostStreamGo :: CostStream -> CostStream -> CostStream
addCostStreamGo (CostLast costL)        costsR = CostCons costL costsR
addCostStreamGo (CostCons costL costsL) costsR = CostCons costL $ addCostStreamGo costsR costsL

-- | Add two streams by interleaving their elements (as opposed to draining out one of the streams
-- before starting to take elements from the other one). No particular reason to prefer
-- interleaving over draining out one of the streams first.
addCostStream :: CostStream -> CostStream -> CostStream
addCostStream costsL0 costsR0 = case (costsL0, costsR0) of
    (CostLast costL, CostLast costR) -> CostLast $ costL + costR
    _                                -> addCostStreamGo costsL0 costsR0
{-# INLINE addCostStream #-}

-- See Note [Global local functions].
-- Didn't attempt to optimize it.
minCostStreamGo :: CostStream -> CostStream -> CostStream
minCostStreamGo costsL costsR =
    -- Peel off a cost from each of the streams, if there's any, compare the two costs, emit
    -- the minimum cost to the outside and recurse. If the two elements aren't equal, then we put
    -- the difference between them back to the stream that had the greatest cost (thus subtracting
    -- the minimum cost from the stream -- since we just accounted for it by lazily emitting it to
    -- the outside). Proceed until one of the streams is drained out.
    let (!costL, !mayCostsL') = unconsCost costsL
        (!costR, !mayCostsR') = unconsCost costsR
        (!costMin, !mayCostsL'', !mayCostsR'') = case costL `compare` costR of
            LT -> (costL, mayCostsL', pure $ reconsCost (costR - costL) mayCostsR')
            EQ -> (costL, mayCostsL', mayCostsR')
            GT -> (costR, pure $ reconsCost (costL - costR) mayCostsL', mayCostsR')
    in reconsCost costMin $ minCostStreamGo <$> mayCostsL'' <*> mayCostsR''

-- | Calculate the minimum of two 'CostStream's. May return a stream that is longer than either of
-- the two (but not more than twice).
minCostStream :: CostStream -> CostStream -> CostStream
minCostStream costsL0 costsR0 = case (costsL0, costsR0) of
    (CostLast costL, CostLast costR) -> CostLast $ min costL costR
    _                                -> minCostStreamGo costsL0 costsR0
{-# INLINE minCostStream #-}
