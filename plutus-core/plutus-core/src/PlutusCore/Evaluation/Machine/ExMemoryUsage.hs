-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module PlutusCore.Evaluation.Machine.ExMemoryUsage
  ( CostRose (..)
  , singletonRose
  , ExMemoryUsage (..)
  , flattenCostRose
  , NumBytesCostedAsNumWords (..)
  , IntegerCostedLiterally (..)
  , ValueTotalSize (..)
  , ValueLogOuterSizeAddLogMaxInnerSize (..)
  ) where

import PlutusCore.Crypto.BLS12_381.G1 as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing as BLS12_381.Pairing
import PlutusCore.Data
import PlutusCore.Evaluation.Machine.CostStream
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Unroll (dropN)
import PlutusCore.Value (Value)
import PlutusCore.Value qualified as Value

import Data.ByteString qualified as BS
import Data.Functor
import Data.Map.Strict qualified as Map
import Data.Proxy
import Data.SatInt
import Data.Text qualified as T
import Data.Vector.Strict (Vector)
import Data.Vector.Strict qualified as Vector
import Data.Word
import GHC.Natural
import GHC.Num.Integer (integerLog2)
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

{-| A lazy tree of costs. Convenient for calculating the costs of values of built-in types, because
they may have arbitrary branching (in particular a 'Data' object can contain a list of 'Data'
objects inside of it).

'CostRose' gets collapsed to a lazy linear structure down the pipeline, so that we can
stream the costs to the outside where, say, the CEK machine picks them up one by one and handles
somehow (in particular, subtracts from the remaining budget). -}
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
      [] -> CostLast cost1
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
        _ -> flattenCostRoseGo rose1' $ forest1' ++ forest2

{-| Collapse a 'CostRose' to a lazy linear stream of costs. Retrieving the next element takes O(1)
time in the worst case regardless of the recursion pattern of the given 'CostRose'. -}
flattenCostRose :: CostRose -> CostStream
flattenCostRose (CostRose cost []) = CostLast cost
flattenCostRose (CostRose cost (rose : forest)) = CostCons cost $ flattenCostRoseGo rose forest
{-# INLINE flattenCostRose #-}

class ExMemoryUsage a where
  -- Inlining the implementations of this method gave us a 1-2% speedup.
  memoryUsage :: a -> CostRose

{- Note [Alternative memory usage instances].  The `memoryUsage` function provides
 a measure of the size of an object for costing purposes, the idea being that
 the time taken to execute a builtin, and the memory used to contain its result,
 will depend on the size of the inputs.  The name `memoryUsage` is perhaps a
 misnomer: it was originally supposed to measure (in 64-bit words) the heap
 space required to store an object, but this is not always the correct measure
 to use.  For example, the time taken by `AddInteger` or `MultiplyInteger` will
 depend on the logarithms of the inputs (and the logarithm is proportional to
 the memory occupied by the inputs), and the memory occupied by the result will
 be some function of the memory occupied by the inputs, so for these functions
 the actual memory usage is a sensible size measure.  However, calling
 `replicateByte n b` function allocates a number of bytes which is equal to the
 actual value of `n`, which will be exponentially greater than the memory
 occupied by `n`, so this case the memory usage is not a sensible size measure.
 In most cases the default `memoryUsage` function returns the actual memory
 usage, but to deal with cases like `replicateByte` we occasionally use newtype
 wrappers which define a different size measure (see `IntegerCostedLiterally`
 below).  Polymorphic types require some care though: see Note [ExMemoryUsage
 for polymorphic types].
-}

{- Note [ExMemoryUsage for polymorphic types].  For polymorphic types such as
 `pair, `list`, and `array` DO NOT use newtype wrappers to define alternative
 size measures.  The denotations of functions which take polymorphic arguments
 use `SomeConstant` and this will ignore newtype wrappers and will only use the
 default `memoryUsage` function, which could lead to unexpected results.
 Furthermore, actual memory usage is typically not a good size measure for
 polymorphic arguments: the time taken to process a list, for example, will
 typically depend only on the length of the list and not the size of the
 contents.  Currently all such functions are parametrically polymorphic and only
 manipulate pointers without inspecting the contents of their polymorphic
 arguments, so it is reasonable to use size measures which depend only on the
 surface structure of polymorphic objects. -}

{- We expect that all builtins which involve pairs will be constant cost and so
   their memory usage will never be involved in any computations.  The memory
   usage is set to maxBound so that we'll notice if this assumption is ever
   violated -}
instance ExMemoryUsage (a, b) where
  memoryUsage _ = singletonRose maxBound
  {-# INLINE memoryUsage #-}

{- Note the the `memoryUsage` of an empty list is zero.  This shouldn't cause any
 problems, but be sure to check that no costing function involving lists can
 return zero for an empty list (or any other input).
-}
{- Calculating the memory usage by processing the spine of the list in batches.
 This avoids forcing the entire list upfront just to compute the length, instead
 producing costs incrementally as CostRose children. Each batch of 100 elements
 produces one cost node, which is more efficient than per-element costing while
 still avoiding full spine traversal before the builtin executes.

 We use 'dropN' which is statically unrolled at compile time via type-level
 programming (see Note [Static loop unrolling] in PlutusCore.Unroll). This
 avoids the overhead of 'splitAt' which allocates a tuple and a new list for
 the prefix. The statically unrolled pattern matching is significantly faster. -}
instance ExMemoryUsage [a] where
  memoryUsage = go
    where
      go xs = case dropN @100 xs of
        Just rest -> CostRose 100 [go rest]
        Nothing -> singletonRose (fromIntegral (length xs))
  {-# INLINE memoryUsage #-}

{- Note the the `memoryUsage` of an empty array is zero.  This shouldn't cause any
 problems, but be sure to check that no costing function involving arrays can
 return zero for an empty array (or any other input).
-}
instance ExMemoryUsage (Vector a) where
  memoryUsage l = singletonRose . fromIntegral $ Vector.length l
  {-# INLINE memoryUsage #-}

instance (Closed uni, uni `Everywhere` ExMemoryUsage) => ExMemoryUsage (Some (ValueOf uni)) where
  memoryUsage (Some (ValueOf uni x)) = bring (Proxy @ExMemoryUsage) uni (memoryUsage x)
  {-# INLINE memoryUsage #-}

instance ExMemoryUsage () where
  memoryUsage () = singletonRose 1
  {-# INLINE memoryUsage #-}

{-| Calculate a 'CostingInteger' for the size of the given 'Integer', measured in
64-bit words.  This is the default size measure for `Integer`s. -}
memoryUsageInteger :: Integer -> CostingInteger
-- integerLog2 is unspecified for 0 (but in practice returns -1)
{-^ This changed with GHC 9.2: it now returns 0.  It's probably safest if we
keep this special case for the time being though. -}
memoryUsageInteger 0 = 1
-- Assume 64-bit words
memoryUsageInteger i = fromIntegral (integerLog2 (abs i) `div` 64 + 1)
-- So that the produced GHC Core doesn't explode in size, we don't win anything by inlining this
-- function anyway.
{-# OPAQUE memoryUsageInteger #-}

instance ExMemoryUsage Integer where
  memoryUsage i = singletonRose $ memoryUsageInteger i
  {-# INLINE memoryUsage #-}

instance ExMemoryUsage Natural where
  -- Same as Integer since we are going via Integer
  memoryUsage n = memoryUsage $ toInteger n
  {-# INLINE memoryUsage #-}

instance ExMemoryUsage Word8 where
  memoryUsage _ = singletonRose 1
  {-# INLINE memoryUsage #-}

{-| When invoking a built-in function, a value of type `NumBytesCostedAsNumWords`
   can be used transparently as a built-in Integer but with a different size
   measure: see Note [Integral types as Integer].  This is required by the
   `integerToByteString` builtin, which takes an argument `w` specifying the
   width (in bytes) of the output bytestring (zero-padded to the desired size).
   The memory consumed by the function is given by `w`, *not* the size of `w`.
   The `NumBytesCostedAsNumWords` type wraps an Int `w` in a newtype whose
   `ExMemoryUsage` is equal to the number of eight-byte words required to
   contain `w` bytes, allowing its costing function to work properly.  We also
   use this for `replicateByte`.  If this is used to wrap an argument in the
   denotation of a builtin then it *MUST* also be used to wrap the same argument
   in the relevant budgeting benchmark. -}
newtype NumBytesCostedAsNumWords = NumBytesCostedAsNumWords {unNumBytesCostedAsNumWords :: Integer}

instance ExMemoryUsage NumBytesCostedAsNumWords where
  memoryUsage (NumBytesCostedAsNumWords n) = singletonRose . fromIntegral $ ((abs n - 1) `div` 8) + 1
  {-# INLINE memoryUsage #-}

-- Note that this uses `fromIntegral`, which will narrow large values to
-- maxBound::SatInt = 2^63-1.  This shouldn't be a problem for costing because no
-- realistic input should be that large; however if you're going to use this then be
-- sure to convince yourself that it's safe.

{-| A wrapper for `Integer`s whose "memory usage" for costing purposes is the
   absolute value of the `Integer`.  This is used for costing built-in functions
   such as `shiftByteString` and `rotateByteString`, where the cost may depend
   on the actual value of the shift argument, not its size.  If this is used to
   wrap an argument in the denotation of a builtin then it *MUST* also be used
   to wrap the same argument in the relevant budgeting benchmark. -}
newtype IntegerCostedLiterally = IntegerCostedLiterally {unIntegerCostedLiterally :: Integer}

instance ExMemoryUsage IntegerCostedLiterally where
  memoryUsage (IntegerCostedLiterally n) = singletonRose . fromIntegral $ abs n
  {-# INLINE memoryUsage #-}

-- Note that this uses `fromIntegral`, which will narrow large values to
-- maxBound::SatInt = 2^63-1.  This shouldn't be a problem for costing because no
-- realistic input should be that large; however if you're going to use this then be
-- sure to convince yourself that it's safe.

{- Bytestrings: we want the empty bytestring and bytestrings of length 1-8 to have
   size 1, bytestrings of length 9-16 to have size 2, etc.  Note that (-1)
   `quot` 8 == 0, so the code below gives the correct answer for the empty
   bytestring.  -}
instance ExMemoryUsage BS.ByteString where
  -- Don't use `div` here!  That gives 0 instead of 1 for the empty bytestring.
  memoryUsage bs = singletonRose . unsafeToSatInt $ ((n - 1) `quot` 8) + 1
    where
      n = BS.length bs
  {-# INLINE memoryUsage #-}

instance ExMemoryUsage T.Text where
  -- This says that @Text@ allocates 1 'CostingInteger' worth of memory (i.e. 8 bytes) per
  -- character, which is a conservative overestimate (i.e. is safe) regardless of whether @Text@
  -- is UTF16-based (like it used to when we implemented this instance) or UTF8-based (like it is
  -- now).
  --
  -- Note that the @ExMemoryUsage Char@ instance does not affect this one, this is for performance
  -- reasons, since @T.length@ is O(1) unlike @sum . map (memoryUsage @Char) . T.unpack@. We used
  -- to have the latter, but changed it to the former for easy performance gains.
  --
  -- We may want to make this a bit less of an overestimate in future just not to overcharge
  -- users.
  memoryUsage = singletonRose . fromIntegral . T.length
  {-# INLINE memoryUsage #-}

instance ExMemoryUsage Int where
  memoryUsage _ = singletonRose 1
  {-# INLINE memoryUsage #-}

-- If you ever change this, also change @ExMemoryUsage T.Text@.
instance ExMemoryUsage Char where
  memoryUsage _ = singletonRose 1
  {-# INLINE memoryUsage #-}

instance ExMemoryUsage Bool where
  memoryUsage _ = singletonRose 1
  {-# INLINE memoryUsage #-}

{-| Add two 'CostRose's. We don't make this into a 'Semigroup' instance, because there exist
different ways to add two 'CostRose's (e.g. we could optimize the case when one of the roses
contains only one element or we can make the function lazy in the second argument). Here we chose
the version that is most efficient when the first argument is a statically known constant (we
didn't do any benchmarking though, so it may not be the most efficient one) as we need this
below. -}
addConstantRose :: CostRose -> CostRose -> CostRose
addConstantRose (CostRose cost1 forest1) (CostRose cost2 forest2) =
  CostRose (cost1 + cost2) (forest1 ++ forest2)
{-# INLINE addConstantRose #-}

{- A naive traversal for size.  This accounts for the number of nodes in a Data
   object and also the sizes of the contents of the nodes.  This is not ideal,
   but it seems to be the best we can do.  At present this only comes into play
   for 'equalsData', which is implemented using the derived implementation of
   '==' (fortunately the costing functions are lazy, so this won't be called for
   things like 'unBData' which have constant costing functions because they only
   have to look at the top node).  The problem is that when we call 'equalsData'
   the comparison will take place entirely in Haskell, so the costing functions
   for the contents of 'I' and 'B' nodes won't be called.  Thus if we just
   counted the number of nodes the sizes of 'I 2' and 'B <huge bytestring>'
   would be the same but they'd take different amounts of time to compare.  It's
   not clear how to trade off the costs of processing a node and processing the
   contents of nodes: the implementation below compromises by charging four
   units per node, but we may wish to revise this after experimentation.
-}
instance ExMemoryUsage Data where
  memoryUsage = sizeData
    where
      dataNodeRose = singletonRose 4
      {-# INLINE dataNodeRose #-}

      sizeData d = addConstantRose dataNodeRose $ case d of
        -- TODO: include the size of the tag, but not just yet. See PLT-1176.
        Constr _ l -> CostRose 0 $ l <&> sizeData
        Map l -> CostRose 0 $ l >>= \(d1, d2) -> [d1, d2] <&> sizeData
        List l -> CostRose 0 $ l <&> sizeData
        I n -> memoryUsage n
        B b -> memoryUsage b
        Array v -> CostRose 0 $ Vector.toList v <&> sizeData

instance ExMemoryUsage Value where
  memoryUsage = singletonRose . fromIntegral . Value.totalSize

-- | Measure the size of a `Value` by its `Value.totalSize`.
newtype ValueTotalSize = ValueTotalSize {unValueTotalSize :: Value}

instance ExMemoryUsage ValueTotalSize where
  memoryUsage = singletonRose . fromIntegral . Value.totalSize . unValueTotalSize

{- Note [ValueLogOuterSizeAddLogMaxInnerSize]
This newtype wrapper measures the sum of logarithms of outer and max inner sizes
for two-level map structures like Value.

For a Value (Map PolicyId (Map TokenName Quantity)), the lookup cost is:
O(log m + log k) where:
  - m is the number of policies (outer map size)
  - k is the maximum number of tokens in any policy (max inner map size)

This is based on experimental evidence showing that two-level map lookup time
scales linearly with the sum of depths (log m + log k), not their maximum.

Used for builtins like lookupCoin where worst-case performance requires
traversing both the outer map to find the policy AND the largest inner map
to find the token.

If this is used to wrap an argument in the denotation of a builtin then it *MUST* also
be used to wrap the same argument in the relevant budgeting benchmark.
-}
newtype ValueLogOuterSizeAddLogMaxInnerSize
  = ValueLogOuterSizeAddLogMaxInnerSize {unValueLogOuterSizeAddLogMaxInnerSize :: Value}

instance ExMemoryUsage ValueLogOuterSizeAddLogMaxInnerSize where
  memoryUsage (ValueLogOuterSizeAddLogMaxInnerSize v) =
    let outerSize = Map.size (Value.unpack v)
        innerSize = Value.maxInnerSize v
        logOuter = if outerSize > 0 then integerLog2 (toInteger outerSize) + 1 else 0
        logInner = if innerSize > 0 then integerLog2 (toInteger innerSize) + 1 else 0
     in singletonRose $ fromIntegral (logOuter + logInner)
  {-# INLINE memoryUsage #-}

{- Note [Costing constant-size types]
The memory usage of each of the BLS12-381 types is constant, so we may be able
to optimise things a little by ensuring that we don't re-compute the size of
(say) a G1 element every time one is used. GHC will probably do this anyway, but
we make sure by defining a top level function for each of the size measures and
getting the memoryUsage instances to call those.
-}

g1ElementCost :: CostRose
g1ElementCost = singletonRose . unsafeToSatInt $ BLS12_381.G1.memSizeBytes `div` 8
{-# OPAQUE g1ElementCost #-}

instance ExMemoryUsage BLS12_381.G1.Element where
  memoryUsage _ = g1ElementCost

-- Should be 18

g2ElementCost :: CostRose
g2ElementCost = singletonRose . unsafeToSatInt $ BLS12_381.G2.memSizeBytes `div` 8
{-# OPAQUE g2ElementCost #-}

instance ExMemoryUsage BLS12_381.G2.Element where
  memoryUsage _ = g2ElementCost

-- Should be 36

mlResultElementCost :: CostRose
mlResultElementCost = singletonRose . unsafeToSatInt $ BLS12_381.Pairing.mlResultMemSizeBytes `div` 8
{-# OPAQUE mlResultElementCost #-}

instance ExMemoryUsage BLS12_381.Pairing.MlResult where
  memoryUsage _ = mlResultElementCost

-- Should be 72
