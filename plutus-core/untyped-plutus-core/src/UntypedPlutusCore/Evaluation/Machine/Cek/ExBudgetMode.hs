-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.ExBudgetMode
  ( ExBudgetMode (..)
  , CountingSt (..)
  , CekExTally (..)
  , TallyingSt (..)
  , RestrictingSt (..)
  , Hashable
  , monoidalBudgeting
  , counting
  , enormousBudget
  , tallying
  , restricting
  , restrictingLarge
  , restrictingEnormous
  )
where

import PlutusPrelude

import UntypedPlutusCore.Evaluation.Machine.Cek.Internal

import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))

import Control.Lens (imap)
import Control.Monad (when)
import Control.Monad.Except
import Data.HashMap.Monoidal as HashMap
import Data.Hashable (Hashable)
import Data.Map.Strict qualified as Map
import Data.Primitive.PrimArray
import Data.STRef
import Data.SatInt
import Data.Semigroup.Generic
import Prettyprinter
import Text.PrettyBy (IgnorePrettyConfig (..))

{-| Construct an 'ExBudgetMode' out of a function returning a value of the budgeting state type.
The value then gets added to the current state via @(<>)@. -}
monoidalBudgeting
  :: Monoid cost => (ExBudgetCategory fun -> ExBudget -> cost) -> ExBudgetMode cost uni fun
monoidalBudgeting toCost = ExBudgetMode $ do
  costRef <- newSTRef mempty
  budgetRef <- newSTRef mempty
  let spend key budgetToSpend = CekM $ do
        modifySTRef' costRef (<> toCost key budgetToSpend)
        modifySTRef' budgetRef (<> budgetToSpend)
      spender = CekBudgetSpender spend
      cumulative = readSTRef budgetRef
      final = readSTRef costRef
  pure $ ExBudgetInfo spender final cumulative

-- | For calculating the cost of execution by counting up using the 'Monoid' instance of 'ExBudget'.
newtype CountingSt = CountingSt ExBudget
  deriving stock (Eq, Show)
  deriving newtype (Semigroup, Monoid, PrettyBy config, NFData)

instance Pretty CountingSt where
  pretty (CountingSt budget) = parens $ "required budget:" <+> pretty budget <> line

-- | For calculating the cost of execution.
counting :: ExBudgetMode CountingSt uni fun
counting = monoidalBudgeting $ const CountingSt

{-| For a detailed report on what costs how much + the same overall budget that 'Counting' gives.
The (derived) 'Monoid' instance of 'CekExTally' is the main piece of the machinery. -}
newtype CekExTally fun = CekExTally (MonoidalHashMap (ExBudgetCategory fun) ExBudget)
  deriving stock (Eq, Generic, Show)
  deriving (Semigroup, Monoid) via (GenericSemigroupMonoid (CekExTally fun))
  deriving anyclass (NFData)
  deriving (PrettyBy config) via (IgnorePrettyConfig (CekExTally fun))

instance (Show fun, Ord fun) => Pretty (CekExTally fun) where
  pretty (CekExTally m) =
    let om = Map.fromList $ HashMap.toList m
     in parens $
          encloseSep "{" "}" "| " $
            fmap group $
              Map.elems $
                imap (\k v -> (pretty k <+> "causes" <+> group (pretty v))) om

data TallyingSt fun = TallyingSt (CekExTally fun) ExBudget
  deriving stock (Eq, Show, Generic)
  deriving (Semigroup, Monoid) via (GenericSemigroupMonoid (TallyingSt fun))
  deriving anyclass (NFData)
  deriving (PrettyBy config) via (IgnorePrettyConfig (TallyingSt fun))

instance (Show fun, Ord fun) => Pretty (TallyingSt fun) where
  pretty (TallyingSt tally budget) =
    parens $
      fold
        [ "{ tally: "
        , pretty tally
        , line
        , "| budget: "
        , pretty budget
        , line
        , "}"
        ]

-- | For a detailed report on what costs how much + the same overall budget that 'Counting' gives.
tallying :: Hashable fun => ExBudgetMode (TallyingSt fun) uni fun
tallying =
  monoidalBudgeting $ \key budgetToSpend ->
    TallyingSt (CekExTally $ singleton key budgetToSpend) budgetToSpend

newtype RestrictingSt = RestrictingSt ExRestrictingBudget
  deriving stock (Eq, Show)
  deriving newtype (Semigroup, Monoid, NFData)
  deriving anyclass (PrettyBy config)

instance Pretty RestrictingSt where
  pretty (RestrictingSt budget) = parens $ "final budget:" <+> pretty budget <> line

-- | For execution, to avoid overruns.
restricting
  :: ThrowableBuiltins uni fun
  => ExRestrictingBudget -> ExBudgetMode RestrictingSt uni fun
restricting (ExRestrictingBudget initB@(ExBudget cpuInit memInit)) = ExBudgetMode $ do
  -- We keep the counters in a PrimArray. This is better than an STRef since it stores its contents unboxed.
  --
  -- If we don't specify the element type then GHC has difficulty inferring it, but it's
  -- annoying to specify the monad, since it refers to the 's' which is not in scope.
  ref <- newPrimArray @_ @SatInt 2
  let
    cpuIx = 0
    memIx = 1
    readCpu = coerce @_ @ExCPU <$> readPrimArray ref cpuIx
    writeCpu cpu = writePrimArray ref cpuIx $ coerce cpu
    readMem = coerce @_ @ExMemory <$> readPrimArray ref memIx
    writeMem mem = writePrimArray ref memIx $ coerce mem

  writeCpu cpuInit
  writeMem memInit
  let
    spend _ (ExBudget cpuToSpend memToSpend) = do
      cpuLeft <- CekM readCpu
      memLeft <- CekM readMem
      let cpuLeft' = cpuLeft - cpuToSpend
      let memLeft' = memLeft - memToSpend
      -- Note that even if we throw an out-of-budget error, we still need to record
      -- what the final state was.
      CekM $ writeCpu cpuLeft'
      CekM $ writeMem memLeft'
      when (cpuLeft' < 0 || memLeft' < 0) $ do
        let
          -- You'd think whether the budget is computed strictly or not before throwing
          -- an error isn't important, but GHC refuses to unbox the second argument of
          -- @spend@ without this bang. Bangs on @cpuLeft'@ and @memLeft'@ don't help
          -- either as those are forced by 'writeCpu' and 'writeMem' anyway. Go figure.
          !budgetLeft = ExBudget cpuLeft' memLeft'
        throwError $
          ErrorWithCause
            (OperationalError (CekOutOfExError $ ExRestrictingBudget budgetLeft))
            Nothing
    spender = CekBudgetSpender spend
    remaining = ExBudget <$> readCpu <*> readMem
    cumulative = do
      r <- remaining
      pure $ initB `minusExBudget` r
    final = RestrictingSt . ExRestrictingBudget <$> remaining
  pure $ ExBudgetInfo spender final cumulative

-- | 'restricting' instantiated at 'largeBudget'.
restrictingLarge :: ThrowableBuiltins uni fun => ExBudgetMode RestrictingSt uni fun
restrictingLarge = restricting largeBudget

-- | 'restricting' instantiated at 'enormousBudget'.
restrictingEnormous :: ThrowableBuiltins uni fun => ExBudgetMode RestrictingSt uni fun
restrictingEnormous = restricting enormousBudget
