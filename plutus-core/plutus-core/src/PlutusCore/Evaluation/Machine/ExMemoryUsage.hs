-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module PlutusCore.Evaluation.Machine.ExMemoryUsage
    ( CostRose(..)
    , ExMemoryUsage(..)
    , flattenCostRose
    ) where

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

-- See Note [Global local functions].
flattenCostRoseGo :: CostRose -> [CostRose] -> CostStream
flattenCostRoseGo (CostRose cost1 forest1) forest2 =
    case forest1 of
        [] -> case forest2 of
            []                -> CostLast cost1
            rose2' : forest2' -> CostCons cost1 $ flattenCostRoseGo rose2' forest2'
        rose1' : forest1' ->
            CostCons cost1 $ case forest1' of
                [] -> flattenCostRoseGo rose1' forest2
                _  -> flattenCostRoseGo rose1' $ forest1' ++ forest2

flattenCostRose :: CostRose -> CostStream
flattenCostRose (CostRose cost [])              = CostLast cost
flattenCostRose (CostRose cost (rose : forest)) = CostCons cost $ flattenCostRoseGo rose forest
{-# INLINE flattenCostRose #-}

class ExMemoryUsage a where
    -- Inlining the implementations of this method gave us a 1-2% speedup.
    memoryUsage :: a -> CostRose -- ^ How much memory does 'a' use?

instance (ExMemoryUsage a, ExMemoryUsage b) => ExMemoryUsage (a, b) where
    memoryUsage (a, b) = CostRose 1 [memoryUsage a, memoryUsage b]
    {-# INLINE memoryUsage #-}

-- See https://github.com/input-output-hk/plutus/issues/1861
instance ExMemoryUsage (SomeTypeIn uni) where
  memoryUsage _ = CostRose 1 [] -- TODO things like @list (list (list integer))@ take up a non-constant amount of space.
  {-# INLINE memoryUsage #-}

-- See https://github.com/input-output-hk/plutus/issues/1861
instance (Closed uni, uni `Everywhere` ExMemoryUsage) => ExMemoryUsage (Some (ValueOf uni)) where
  -- TODO this is just to match up with existing golden tests. We probably need to account for @uni@ as well.
  memoryUsage (Some (ValueOf uni x)) = bring (Proxy @ExMemoryUsage) uni (memoryUsage x)
  {-# INLINE memoryUsage #-}

instance ExMemoryUsage () where
  memoryUsage () = CostRose 1 []
  {-# INLINE memoryUsage #-}

memoryUsageInteger :: Integer -> CostingInteger
-- integerLog2# is unspecified for 0 (but in practice returns -1)
memoryUsageInteger 0 = 1
-- Assume 64 Int
memoryUsageInteger i = fromIntegral $ I# (integerLog2# (abs i) `quotInt#` integerToInt 64) + 1
-- So that the produced GHC Core doesn't explode in size, we don't win anything by inlining this
-- function anyway.
{-# NOINLINE memoryUsageInteger #-}

instance ExMemoryUsage Integer where
  memoryUsage i = CostRose (memoryUsageInteger i) [] where
  {-# INLINE memoryUsage #-}

instance ExMemoryUsage Word8 where
  memoryUsage _ = CostRose 1 []
  {-# INLINE memoryUsage #-}

{- Bytestrings: we want things of length 0 to have size 0, 1-8 to have size 1,
   9-16 to have size 2, etc.  Note that (-1) div 8 == -1, so the code below
   gives the correct answer for the empty bytestring.  Maybe we should just use
   1 + (toInteger $ BS.length bs) `div` 8, which would count one extra for
   things whose sizes are multiples of 8. -}
instance ExMemoryUsage BS.ByteString where
  -- Don't use `div` here!  That gives 1 instead of 0 for n=0.
  memoryUsage bs = CostRose (unsafeToSatInt $ ((n - 1) `quot` 8) + 1) [] where
      n = BS.length bs
  {-# INLINE memoryUsage #-}

instance ExMemoryUsage T.Text where
  -- This is slow and inaccurate, but matches the version that was originally deployed.
  -- We may try and improve this in future so long as the new version matches this exactly.
  memoryUsage text = memoryUsage $ T.unpack text
  {-# INLINE memoryUsage #-}

instance ExMemoryUsage Int where
  memoryUsage _ = CostRose 1 []
  {-# INLINE memoryUsage #-}

instance ExMemoryUsage Char where
  memoryUsage _ = CostRose 1 []
  {-# INLINE memoryUsage #-}

instance ExMemoryUsage Bool where
  memoryUsage _ = CostRose 1 []
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
{- This code runs on the chain and hence should be as efficient as possible. To
   that end it's tempting to make these functions strict and tail recursive (and
   similarly in the instance for lists above), but experiments showed that that
   didn't improve matters and in fact some versions led to a slight slowdown.
-}
instance ExMemoryUsage Data where
    memoryUsage = sizeData where
        nodeMem = CostRose 4 []
        {-# INLINE nodeMem #-}

        combine (CostRose cost1 forest1) (CostRose cost2 forest2) =
            CostRose (cost1 + cost2) (forest1 ++ forest2)
        {-# INLINE combine #-}

        sizeData d = combine nodeMem $ case d of
            -- TODO: include the size of the tag, but not just yet.  See SCP-3677.
            Constr _ l -> CostRose 0 $ l <&> sizeData
            Map l      -> CostRose 0 $ l <&> \(d1, d2) -> CostRose 0 $ [d1, d2] <&> sizeData
            List l     -> CostRose 0 $ l <&> sizeData
            I n        -> memoryUsage n
            B b        -> memoryUsage b
