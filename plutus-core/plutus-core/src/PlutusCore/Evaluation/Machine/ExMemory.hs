-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}

module PlutusCore.Evaluation.Machine.ExMemory
    ( CostingInteger
    , ExMemory(..)
    , ExCPU(..)
    ) where

import Codec.Serialise (Serialise)
import Control.DeepSeq
import Data.Aeson
import Data.SatInt
import Data.Semigroup
import GHC.Generics
import Language.Haskell.TH.Syntax (Lift)
import NoThunks.Class
import Text.Pretty
import Text.PrettyBy

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
  deriving newtype (Num, NFData, Read, Bounded)
  deriving (FromJSON, ToJSON) via CostingInteger
  deriving Serialise via CostingInteger
  deriving anyclass NoThunks
instance Pretty ExMemory where
    pretty (ExMemory i) = pretty (unSatInt i)
instance PrettyBy config ExMemory where
    prettyBy _ m = pretty m

-- Defining manually, because the 'Sum' instance doesn't have the @INLINE@ pragmas causing
instance Semigroup ExMemory where
    (<>) = (+)
    {-# INLINE (<>) #-}

    stimes n mem = fromIntegral n * mem
    {-# INLINE stimes #-}

instance Monoid ExMemory where
    mempty = ExMemory 0
    {-# INLINE mempty #-}

-- | Counts CPU units in picoseconds: maximum value for SatInt is 2^63 ps, or
-- appproximately 106 days.
newtype ExCPU = ExCPU CostingInteger
  deriving stock (Eq, Ord, Show, Generic, Lift)
  deriving newtype (Num, NFData, Read, Bounded)
  deriving (FromJSON, ToJSON) via CostingInteger
  deriving Serialise via CostingInteger
  deriving anyclass NoThunks
instance Pretty ExCPU where
    pretty (ExCPU i) = pretty (unSatInt i)
instance PrettyBy config ExCPU where
    prettyBy _ m = pretty m

instance Semigroup ExCPU where
    (<>) = (+)
    {-# INLINE (<>) #-}

    stimes n mem = fromIntegral n * mem
    {-# INLINE stimes #-}

instance Monoid ExCPU where
    mempty = ExCPU 0
    {-# INLINE mempty #-}
