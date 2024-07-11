-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module PlutusCore.Evaluation.Machine.ExMemoryUsage
    ( CostRose(..)
    , singletonRose
    , ExMemoryUsage(..)
    , flattenCostRose
    , NumBytesCostedAsNumWords(..)
    , IntegerCostedLiterally(..)
    , ListCostedByLength(..)
    ) where

import PlutusCore.Crypto.BLS12_381.G1 as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing as BLS12_381.Pairing
import PlutusCore.Data
import PlutusCore.Evaluation.Machine.CostStream
import PlutusCore.Evaluation.Machine.ExMemory

import Data.ByteString qualified as BS
import Data.Functor
import Data.Proxy
import Data.SatInt
import Data.Text qualified as T
import Data.Word
import GHC.Exts (Int (I#))
import GHC.Integer
import GHC.Integer.Logarithms
import GHC.Prim
import Universe

{-
 ************************************************************************************
 *  WARNING: exercise caution when altering the ExMemoryUsage instances here.       *
 *                                                                                  *
 *  The instances defined in this file will be used to calculate script validation  *
 *  costs, and if an instance is changed then any scripts which were deployed when  *
 *  a previous instance was in effect MUST STILL VALIDATE using the new instance.   *
 *  It is unsafe to increase the memory usage of a type because that may increase   *
 *  the resource usage of existing scripts beyond the limits set (and paid for)     *
 *  when they were uploaded to the chain, but because our costing functions are all *
 *  monotone it is safe to decrease memory usage, as long it decreases for *all*    *
 *  possible values of the type.                                                    *
 ************************************************************************************
-}

{- Note [ExMemoryUsage instances for non-constants]
In order to calculate the cost of a built-in function we need to feed the 'ExMemory' of each
argument to the costing function associated with the builtin. For a polymorphic builtin this means
that we need to be able to compute the 'ExMemory' of the AST provided as an argument to the builtin.
How do we do that? Our strategy is:

1. if the AST is a wrapped constant, then calculate the 'ExMemory' of the constant
2. if the AST is something else, return 1

This is pretty reasonable: a polymorphic builtin *is* allowed to check if the AST that it got as an
argument is a constant or not, and if it happens to be a constant, the builtin *is* allowed to use
it whatever way it wishes (see Note [Builtins and Plutus type checking] for details). Hence a
builtin may in fact do something ad hoc for constants and we need to account for this possibility in
the costing machinery.

But if the given AST is not a constant, the builtin can't do anything else with it, hence we simply
return 1, meaning "the costing function can't use this 'ExMemory' in any non-vacuous way".

See 'HasMeaningIn' for a full list of constraints determining what a builtin can do with values.

However for all types of values, except the one used by the production evaluator, we implement
'ExMemoryUsage' as a call to 'error'. Not because other evaluators don't compute costs during
evaluation -- the CK machine for example does in fact compute them (because we share the same
builtins machinery between all the evaluators and we want it to be efficient on the production path,
hence it's easier to optimize it for all evaluators than just for the single production evaluator).
And not because the resulting 'ExBudget' is not forced by an evaluator that doesn't care about
costing -- it still gets forced (for the same reason).

The actual reason why we call 'error' is because at the moment no builtin is supposed to have a
costing function that actually computes the 'ExMemory' of the given AST. Currently, if the builtin
takes an 'Opaque', it's not supposed to actually look inside of it (unlike with 'SomeConstant') and
hence the costing function is supposed to ignore that argument. It is possible that we'll eventually
decide to add such a builtin, so the current approach of throwing an 'error' is a precaution
ensuring that we won't add any weirdness by accident.

We don't call 'error' on the production path, because we don't want this risk in there. A failing
test is fine, a failing reasonable transaction is not and we don't want to risk it, even if it seems
very unlikely that such a failure could slip in.

The way we ignore arguments in costing functions is by computing the 'ExMemory' of each of those
arguments lazily. I.e. a call to 'memoryUsage' can only be forced within a costing function and
never outside of one. We have to do this regardless of all the reasoning above: if we compute
the 'ExMemory' of, say, a list strictly, then a builtin prepending an element to a list will
have the complexity of O(length_of_the_list) (because computing the 'ExMemory' of a list requires
traversing the list), while we of course want it to be O(1).
-}

-- | A lazy tree of costs. Convenient for calculating the costs of values of built-in types, because
-- they may have arbitrary branching (in particular a 'Data' object can contain a list of 'Data'
-- objects inside of it).
--
-- 'CostRose' gets collapsed to a lazy linear structure down the pipeline, so that we can
-- stream the costs to the outside where, say, the CEK machine picks them up one by one and handles
-- somehow (in particular, subtracts from the remaining budget).
data CostRose = CostRose {-# UNPACK #-} !CostingInteger ![CostRose]
    deriving stock (Show)

-- | Create a 'CostRose' containing a single cost.
singletonRose :: CostingInteger -> CostRose
singletonRose cost = CostRose cost []
{-# INLINE singletonRose #-}

-- See Note [Global local functions].
-- This is one way to define the worker. There are many more, see
-- https://github.com/IntersectMBO/plutus/pull/5239#discussion_r1151197471
-- We chose this one, because it's the simplest (no CPS shenanigans) among the safest (retrieving
-- the next element takes O(1) time in the worst case).
--
-- The algorithm is a variation of the defunctionalization technique (see this post in particular:
-- https://www.joachim-breitner.de/blog/778-Don%e2%80%99t_think,_just_defunctionalize), except we
-- don't want a tail-recursive loop and instead emit costs lazily to the outside (as it's the whole
-- point of the lazy costing approach)
flattenCostRoseGo :: CostRose -> [CostRose] -> CostStream
flattenCostRoseGo (CostRose cost1 forest1) forest2 =
    case forest1 of
        -- The current subtree doesn't have its own subtrees.
        [] -> case forest2 of
            -- No more elements in the entire tree, emit the last cost.
            []                -> CostLast cost1
            -- There's at least one unhandled subtree encountered earlier, emit the current cost
            -- and collapse the unhandled subtree.
            rose2' : forest2' -> CostCons cost1 $ flattenCostRoseGo rose2' forest2'
        -- The current subtree has at least one its own subtree.
        rose1' : forest1' ->
            -- Emit the current cost and handle the list of subtrees of the current subtree.
            CostCons cost1 $ case forest1' of
                -- Same as the case below, except this one avoids creating a chain of
                -- @[] ++ ([] ++ ([] ++ <...>))@, which would make retrieving the next element an
                -- O(depth_of_the_tree) operation in the worst case.
                [] -> flattenCostRoseGo rose1' forest2
                -- Add the remaining subtrees of the current subtree (@forest1'@) to the stack of
                -- all other subtrees (@forest2@) and handle the new current subtree (@rose1'@).
                _  -> flattenCostRoseGo rose1' $ forest1' ++ forest2

-- | Collapse a 'CostRose' to a lazy linear stream of costs. Retrieving the next element takes O(1)
-- time in the worst case regardless of the recursion pattern of the given 'CostRose'.
flattenCostRose :: CostRose -> CostStream
flattenCostRose (CostRose cost [])              = CostLast cost
flattenCostRose (CostRose cost (rose : forest)) = CostCons cost $ flattenCostRoseGo rose forest
{-# INLINE flattenCostRose #-}

class ExMemoryUsage a where
    -- Inlining the implementations of this method gave us a 1-2% speedup.
    memoryUsage :: a -> CostRose

instance (ExMemoryUsage a, ExMemoryUsage b) => ExMemoryUsage (a, b) where
    memoryUsage (a, b) = CostRose 1 [memoryUsage a, memoryUsage b]
    {-# INLINE memoryUsage #-}

instance ExMemoryUsage (SomeTypeIn uni) where
    memoryUsage _ = singletonRose 1
    {-# INLINE memoryUsage #-}

instance (Closed uni, uni `Everywhere` ExMemoryUsage) => ExMemoryUsage (Some (ValueOf uni)) where
    memoryUsage (Some (ValueOf uni x)) = bring (Proxy @ExMemoryUsage) uni (memoryUsage x)
    {-# INLINE memoryUsage #-}

instance ExMemoryUsage () where
    memoryUsage () = singletonRose 1
    {-# INLINE memoryUsage #-}

{- | When invoking a built-in function, a value of type `NumBytesCostedAsNumWords`
   can be used transparently as a built-in Integer but with a different size
   measure: see Note [Integral types as Integer].  This is required by the
   `integerToByteString` builtin, which takes an argument `w` specifying the
   width (in bytes) of the output bytestring (zero-padded to the desired size).
   The memory consumed by the function is given by `w`, *not* the size of `w`.
   The `NumBytesCostedAsNumWords` type wraps an Integer `w` in a newtype whose
   `ExMemoryUsage` is equal to the number of eight-byte words required to
   contain `w` bytes, allowing its costing function to work properly.  We also
   use this for `replicateByte`.  If this is used to wrap an argument in the
   denotation of a builtin then it *MUST* also be used to wrap the same argument
   in the relevant budgeting benchmark.
-}
newtype NumBytesCostedAsNumWords = NumBytesCostedAsNumWords { unNumBytesCostedAsNumWords :: Integer }
instance ExMemoryUsage NumBytesCostedAsNumWords where
    memoryUsage (NumBytesCostedAsNumWords n) = singletonRose . fromIntegral $ ((n-1) `div` 8) + 1
    {-# INLINE memoryUsage #-}

{- | A wrapper for Integers whose "memory usage" for costing purposes is the
   absolute value of the integer.  This is used for costing built-in functions
   such as `shiftByteString` and `rotateByteString`, where the cost may depend
   on the actual value of the shift argument, not its size.  If this is used to
   wrap an argument in the denotation of a builtin then it *MUST* also be used
   to wrap the same argument in the relevant budgeting benchmark.
-}
newtype IntegerCostedLiterally = IntegerCostedLiterally { unIntegerCostedLiterally :: Integer }
instance ExMemoryUsage IntegerCostedLiterally where
    memoryUsage (IntegerCostedLiterally n) = singletonRose . fromIntegral $ abs n
    {-# INLINE memoryUsage #-}

{- | A wrappper for lists whose "memory usage" for costing purposes is just the
   length of the list, ignoring the sizes of the elements. If this is used to
   wrap an argument in the denotation of a builtin then it *MUST* also be used
   to wrap the same argument in the relevant budgeting benchmark. -}
newtype ListCostedByLength a = ListCostedByLength { unListCostedByLength :: [a] }
instance ExMemoryUsage (ListCostedByLength a) where
    memoryUsage (ListCostedByLength l) = singletonRose . fromIntegral $ length l
    {-# INLINE memoryUsage #-}

-- | Calculate a 'CostingInteger' for the given 'Integer'.
memoryUsageInteger :: Integer -> CostingInteger
-- integerLog2# is unspecified for 0 (but in practice returns -1)
-- ^ This changed with GHC 9.2: it now returns 0.  It's probably safest if we
-- keep this special case for the time being though.
memoryUsageInteger 0 = 1
-- Assume 64 Int
memoryUsageInteger i = fromIntegral $ I# (integerLog2# (abs i) `quotInt#` integerToInt 64) + 1
-- So that the produced GHC Core doesn't explode in size, we don't win anything by inlining this
-- function anyway.
{-# NOINLINE memoryUsageInteger #-}

instance ExMemoryUsage Integer where
    memoryUsage i = singletonRose $ memoryUsageInteger i
    {-# INLINE memoryUsage #-}

instance ExMemoryUsage Word8 where
    memoryUsage _ = singletonRose 1
    {-# INLINE memoryUsage #-}

{- Bytestrings: we want the empty bytestring and bytestrings of length 1-8 to have
   size 1, bytestrings of length 9-16 to have size 2, etc.  Note that (-1)
   `quot` 8 == 0, so the code below gives the correct answer for the empty
   bytestring.  -}
instance ExMemoryUsage BS.ByteString where
    -- Don't use `div` here!  That gives 0 instead of 1 for the empty bytestring.
    memoryUsage bs = singletonRose . unsafeToSatInt $ ((n - 1) `quot` 8) + 1 where
        n = BS.length bs
    {-# INLINE memoryUsage #-}

instance ExMemoryUsage T.Text where
    -- This is slow and inaccurate, but matches the version that was originally deployed.
    -- We may try and improve this in future so long as the new version matches this exactly.
    memoryUsage text = memoryUsage $ T.unpack text
    {-# INLINE memoryUsage #-}

instance ExMemoryUsage Int where
    memoryUsage _ = singletonRose 1
    {-# INLINE memoryUsage #-}

instance ExMemoryUsage Char where
    memoryUsage _ = singletonRose 1
    {-# INLINE memoryUsage #-}

instance ExMemoryUsage Bool where
    memoryUsage _ = singletonRose 1
    {-# INLINE memoryUsage #-}

instance ExMemoryUsage a => ExMemoryUsage [a] where
    memoryUsage = CostRose 0 . map memoryUsage
    {-# INLINE memoryUsage #-}

{- Another naive traversal for size.  This accounts for the number of nodes in
   a Data object, and also the sizes of the contents of the nodes.  This is not
   ideal, but it seems to be the best we can do.  At present this only comes
   into play for 'equalsData', which is implemented using the derived
   implementation of '==' (fortunately the costing functions are lazy, so this
   won't be called for things like 'unBData' which have constant costing
   functions because they only have to look at the top node).  The problem is
   that when we call 'equalsData' the comparison will take place entirely in
   Haskell, so the costing functions for the contents of 'I' and 'B' nodes
   won't be called.  Thus if we just counted the number of nodes the sizes of
   'I 2' and 'B <huge bytestring>' would be the same but they'd take different
   amounts of time to compare.  It's not clear how to trade off the costs of
   processing a node and processing the contents of nodes: the implementation
   below compromises by charging four units per node, but we may wish to revise
   this after experimentation.
-}
instance ExMemoryUsage Data where
    memoryUsage = sizeData where
        -- The cost of each node of the 'Data' object (in addition to the cost of its content).
        nodeMem = singletonRose 4
        {-# INLINE nodeMem #-}

        -- Add two 'CostRose's. We don't make this into a 'Semigroup' instance, because there exist
        -- different ways to add two 'CostRose's (e.g. we could optimize the case when one of the
        -- roses contains only one element or we can make the function lazy in the second argument).
        -- Here we chose the version that is most efficient when the first argument is @nodeMem@ (we
        -- didn't do any benchmarking though, so it may not be the most efficient one) -- we don't
        -- have any other cases.
        combine (CostRose cost1 forest1) (CostRose cost2 forest2) =
            CostRose (cost1 + cost2) (forest1 ++ forest2)
        {-# INLINE combine #-}

        sizeData d = combine nodeMem $ case d of
            -- TODO: include the size of the tag, but not just yet.  See SCP-3677.
            Constr _ l -> CostRose 0 $ l <&> sizeData
            Map l      -> CostRose 0 $ l >>= \(d1, d2) -> [d1, d2] <&> sizeData
            List l     -> CostRose 0 $ l <&> sizeData
            I n        -> memoryUsage n
            B b        -> memoryUsage b


{- Note [Costing constant-size types]
The memory usage of each of the BLS12-381 types is constant, so we may be able
to optimise things a little by ensuring that we don't re-compute the size of
(say) a G1 element every time one is used. GHC will probably do this anyway, but
we make sure by defining a top level function for each of the size measures and
getting the memoryUsage instances to call those.
-}

{-# NOINLINE g1ElementCost #-}
g1ElementCost :: CostRose
g1ElementCost = singletonRose . unsafeToSatInt $ BLS12_381.G1.memSizeBytes `div` 8

instance ExMemoryUsage BLS12_381.G1.Element where
    memoryUsage _ = g1ElementCost
    -- Should be 18

{-# NOINLINE g2ElementCost #-}
g2ElementCost :: CostRose
g2ElementCost = singletonRose . unsafeToSatInt $ BLS12_381.G2.memSizeBytes `div` 8

instance ExMemoryUsage BLS12_381.G2.Element where
    memoryUsage _ = g2ElementCost
    -- Should be 36

{-# NOINLINE mlResultElementCost #-}
mlResultElementCost :: CostRose
mlResultElementCost = singletonRose . unsafeToSatInt $ BLS12_381.Pairing.mlResultMemSizeBytes `div` 8

instance ExMemoryUsage BLS12_381.Pairing.MlResult where
    memoryUsage _ = mlResultElementCost
    -- Should be 72
