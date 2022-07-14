{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MagicHash             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Evaluation.Machine.ExMemory
( CostingInteger
, ExMemory(..)
, ExCPU(..)
, ExMemoryUsage(..)
) where

import PlutusCore.Data
import PlutusCore.Name
import PlutusCore.Pretty
import PlutusPrelude

import Control.Monad.RWS.Strict
import Data.Aeson
import Data.ByteString qualified as BS
import Data.Proxy
import Data.SatInt
import Data.Text qualified as T
import GHC.Exts (Int (I#))
import GHC.Integer
import GHC.Integer.Logarithms
import GHC.Prim
import Language.Haskell.TH.Syntax (Lift)
import NoThunks.Class
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
 *  monotone) it is safe to decrease memory usage, as long it decreases for *all*   *
 *  possible values of the type.                                                    *
 ************************************************************************************
-}


{- Note [Memory Usage for Plutus]

The base unit is 'ExMemory', which corresponds to machine words. For primitives,
we use static values for the size, see the corresponding instances. For
composite data types, the Generic instance is used, + 1 for the constructor tag.
For ADTs, the currently selected branch is counted, not the maximum value.
Memory usage of the annotation is not counted, because this should be
abstractly specifiable. It's an implementation detail.

-}

{- Note [Integer types for costing]
We care about the speed of our integer operations for costing, this has a significant effect on speed.
But we also need to care about overflow: the cost counters overflowing is a potential attack!

We have a few choices here for what to do with an overflow:
- Don't (this is what 'Integer' does, it's unbounded)
- Wrap (this is what 'Int'/'Int64' and friends do)
- Throw an overflow error (this is what 'Data.SafeInt' does)
- Saturate (i.e. return max/min bound, this is what 'Data.SatInt does)

In our case
- Not overflowing would be nice, but 'Integer' is significantly slower than the other types.
- Wrapping is quite dangerous, as it could lead to us getting attacked by someone wrapping
their cost around to something that looks below the budget.
- Throwing would be okay, but we'd have to worry about exception catching.
- Saturating is actually quite nice: we care about whether `a op b < budget`. So long as `budget < maxBound`,
  then `a op b < budget` will have the same truth value *regardless* of whether the operation overflows and saturates,
  since saturating implies `a op b >= maxBound > budget`. Plus, it means we don't need to deal with
  exceptions.

So we use 'Data.SatInt', a variant of 'Data.SafeInt' that does saturating arithmetic.

'SatInt' is quite fast, but not quite as fast as using 'Int64' directly (I don't know
why that would be, apart from maybe just the overflow checks), but the wrapping behaviour
of 'Int64' is unacceptable.

One other wrinkle is that 'SatInt' is backed by an 'Int' (i.e. a machine integer
with platform-dependent size), rather than an 'Int64' since the primops that we
need are only available for 'Int' until GHC 9.2 or so. So on 32bit platforms, we
would have much less headroom.

However, we don't build on 32bit platforms anyway, so we can ignore that.
-}

-- See Note [Integer types for costing]
-- See also Note [Budgeting units] in ExBudget.hs
type CostingInteger = SatInt

-- | Counts size in machine words.
newtype ExMemory = ExMemory CostingInteger
  deriving stock (Eq, Ord, Show, Generic, Lift)
  deriving newtype (Num, NFData)
  deriving (Semigroup, Monoid) via (Sum CostingInteger)
  deriving (FromJSON, ToJSON) via CostingInteger
  deriving anyclass NoThunks
instance Pretty ExMemory where
    pretty (ExMemory i) = pretty (toInteger i)
instance PrettyBy config ExMemory where
    prettyBy _ m = pretty m

-- | Counts CPU units in picoseconds: maximum value for SatInt is 2^63 ps, or
-- appproximately 106 days.
newtype ExCPU = ExCPU CostingInteger
  deriving stock (Eq, Ord, Show, Generic, Lift)
  deriving newtype (Num, NFData)
  deriving (Semigroup, Monoid) via (Sum CostingInteger)
  deriving (FromJSON, ToJSON) via CostingInteger
  deriving anyclass NoThunks
instance Pretty ExCPU where
    pretty (ExCPU i) = pretty (toInteger i)
instance PrettyBy config ExCPU where
    prettyBy _ m = pretty m

class ExMemoryUsage a where
    memoryUsage :: a -> ExMemory -- ^ How much memory does 'a' use?

instance (ExMemoryUsage a, ExMemoryUsage b) => ExMemoryUsage (a, b) where
    memoryUsage (a, b) = 1 <> memoryUsage a <> memoryUsage b
instance ExMemoryUsage SatInt where
    memoryUsage n = memoryUsage (fromIntegral @SatInt @Int n)
deriving newtype instance ExMemoryUsage ExMemory
deriving newtype instance ExMemoryUsage Unique

-- See https://github.com/input-output-hk/plutus/issues/1861
instance ExMemoryUsage (SomeTypeIn uni) where
  memoryUsage _ = 1 -- TODO things like @list (list (list integer))@ take up a non-constant amount of space.

-- See https://github.com/input-output-hk/plutus/issues/1861
instance (Closed uni, uni `Everywhere` ExMemoryUsage) => ExMemoryUsage (Some (ValueOf uni)) where
  -- TODO this is just to match up with existing golden tests. We probably need to account for @uni@ as well.
  memoryUsage (Some (ValueOf uni x)) = bring (Proxy @ExMemoryUsage) uni (memoryUsage x)

instance ExMemoryUsage () where
  memoryUsage () = 1

instance ExMemoryUsage Integer where
  memoryUsage 0 = ExMemory 1  -- integerLog2# is unspecified for 0 (but in practice returns -1)
  memoryUsage i = ExMemory $ fromIntegral $ (I# n) + 1
                               where n = (integerLog2# (abs i) `quotInt#` integerToInt 64) :: Int#
                               -- Assume 64-bit size for Integer

{- Bytestrings: we want things of length 0 to have size 0, 1-8 to have size 1,
   9-16 to have size 2, etc.  Note that (-1) div 8 == -1, so the code below
   gives the correct answer for the empty bytestring.  Maybe we should just use
   1 + (toInteger $ BS.length bs) `div` 8, which would count one extra for
   things whose sizes are multiples of 8. -}
instance ExMemoryUsage BS.ByteString where
  memoryUsage bs = ExMemory $ ((n-1) `quot` 8) + 1  -- Don't use `div` here!  That gives 1 instead of 0 for n=0.
      where n = fromIntegral $ BS.length bs :: SatInt

instance ExMemoryUsage T.Text where
  -- This is slow and inaccurate, but matches the version that was originally deployed.
  -- We may try and improve this in future so long as the new version matches this exactly.
  memoryUsage text = memoryUsage $ T.unpack text

instance ExMemoryUsage Int where
  memoryUsage _ = 1

instance ExMemoryUsage Char where
  memoryUsage _ = 1

instance ExMemoryUsage Bool where
  memoryUsage _ = 1

-- Memory usage for lists: let's just go for a naive traversal for now.
instance ExMemoryUsage a => ExMemoryUsage [a] where
    memoryUsage = sizeList
        where sizeList =
                  \case
                   []   -> 0
                   x:xs -> memoryUsage x + sizeList xs

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
    memoryUsage = sizeData
        where sizeData d =
                  nodeMem +
                     case d of
                       Constr _ l -> sizeDataList l
                       Map l      -> sizeDataPairs l
                       List l     -> sizeDataList l
                       I n        -> memoryUsage n
                       B b        -> memoryUsage b
              nodeMem = 4
              sizeDataList []     = 0
              sizeDataList (d:ds) = sizeData d + sizeDataList ds
              sizeDataPairs []           = 0
              sizeDataPairs ((d1,d2):ps) = sizeData d1 + sizeData d2 + sizeDataPairs ps
