{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# LANGUAGE StrictData            #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.ExBudgetMode
    ( ExBudgetMode (..)
    , CountingSt (..)
    , CekExTally (..)
    , TallyingSt (..)
    , RestrictingSt (..)
    , Hashable
    , counting
    , enormousBudget
    , tallying
    , restricting
    , restrictingEnormous
    )
where

import           PlutusPrelude

import           UntypedPlutusCore.Evaluation.Machine.Cek.Internal

import           PlutusCore.Evaluation.Machine.ExBudget
import           PlutusCore.Evaluation.Machine.ExMemory            (ExCPU (..), ExMemory (..))
import           PlutusCore.Evaluation.Machine.Exception

import           Control.Lens                                      (ifoldMap)
import           Control.Monad.Except
import           Control.Monad.ST
import           Data.HashMap.Monoidal                             as HashMap
import           Data.Hashable                                     (Hashable)
import           Data.List                                         (intersperse)
import qualified Data.Map.Strict                                   as Map
import           Data.STRef
import           Data.Semigroup.Generic
import           Data.Text.Prettyprint.Doc
import           Text.PrettyBy                                     (IgnorePrettyConfig (..))

-- | Construct an 'ExBudgetMode' out of a function returning a value of the budgeting state type.
-- The value then gets added to the current state via @(<>)@.
monoidalBudgeting
    :: Monoid cost
    => (ExBudgetCategory fun -> ExBudget -> cost)
    -> ST s (ExBudgetMode cost uni fun s)
monoidalBudgeting toCost = do
    costRef <- newSTRef mempty
    let spender key budgetToSpend = liftST $ modifySTRef' costRef (<> toCost key budgetToSpend)
    pure . ExBudgetMode (CekBudgetSpender spender) $ readSTRef costRef

-- | For calculating the cost of execution by counting up using the 'Monoid' instance of 'ExBudget'.
newtype CountingSt = CountingSt ExBudget
    deriving stock (Eq, Show)
    deriving newtype (Semigroup, Monoid, PrettyBy config, NFData)

instance Pretty CountingSt where
    pretty (CountingSt budget) = parens $ "required budget:" <+> pretty budget <> line

-- | For calculating the cost of execution.
counting :: ST s (ExBudgetMode CountingSt uni fun s)
counting = monoidalBudgeting $ const CountingSt

-- | For a detailed report on what costs how much + the same overall budget that 'Counting' gives.
-- The (derived) 'Monoid' instance of 'CekExTally' is the main piece of the machinery.
newtype CekExTally fun = CekExTally (MonoidalHashMap (ExBudgetCategory fun) ExBudget)
    deriving stock (Eq, Generic, Show)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid (CekExTally fun))
    deriving anyclass (NFData)
    deriving (PrettyBy config) via (IgnorePrettyConfig (CekExTally fun))

instance (Show fun, Ord fun) => Pretty (CekExTally fun) where
    pretty (CekExTally m) =
        let om = Map.fromList $ HashMap.toList m
        in parens $ fold (["{ "] <> (intersperse (line <> "| ") $ fmap group $
          ifoldMap (\k v -> [(pretty k <+> "causes" <+> pretty v)]) om) <> ["}"])

data TallyingSt fun = TallyingSt (CekExTally fun) ExBudget
    deriving stock (Eq, Show, Generic)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid (TallyingSt fun))
    deriving anyclass (NFData)
    deriving (PrettyBy config) via (IgnorePrettyConfig (TallyingSt fun))

instance (Show fun, Ord fun) => Pretty (TallyingSt fun) where
    pretty (TallyingSt tally budget) = parens $ fold
        [ "{ tally: ", pretty tally, line
        , "| budget: ", pretty budget, line
        , "}"
        ]

-- | For a detailed report on what costs how much + the same overall budget that 'Counting' gives.
tallying :: (Eq fun, Hashable fun) => ST s (ExBudgetMode (TallyingSt fun) uni fun s)
tallying =
    monoidalBudgeting $ \key budgetToSpend ->
        TallyingSt (CekExTally $ singleton key budgetToSpend) budgetToSpend

-- data ExBudget = ExBudget { _exBudgetCPU :: ExCPU, _exBudgetMemory :: ExMemory }
-- newtype ExRestrictingBudget = ExRestrictingBudget ExBudget deriving (Show, Eq)

newtype RestrictingSt = RestrictingSt ExRestrictingBudget
    deriving stock (Eq, Show)
    deriving newtype (NFData)
    deriving anyclass (PrettyBy config)

instance Pretty RestrictingSt where
    pretty (RestrictingSt budget) = parens $ "final budget:" <+> pretty budget <> line

-- | For execution, to avoid overruns.
restricting :: ExRestrictingBudget -> ST s (ExBudgetMode RestrictingSt uni fun s)
restricting budget = do
    budgetRef <- newSTRef $ RestrictingSt budget
    let spend _ budgetToSpend = do
            RestrictingSt budgetLeft <- liftST $ readSTRef budgetRef
            let budgetLeft' = budgetLeft `minusExBudget` budgetToSpend
            -- Note that even if we throw an out-of-budget error, we still need to record
            -- what the final state was.
            liftST . writeSTRef budgetRef $! RestrictingSt budgetLeft'
            when (isNegativeBudget budgetLeft') $
                throwingWithCause _EvaluationError
                    (UserEvaluationError $ CekOutOfExError budgetLeft')
                    Nothing
    pure . ExBudgetMode (CekBudgetSpender spend) $ readSTRef budgetRef

-- | When we want to just evaluate the program we use the 'Restricting' mode with an enormous
-- budget, so that evaluation costs of on-chain budgeting are reflected accurately in benchmarks.
enormousBudget :: ExRestrictingBudget
enormousBudget = ExRestrictingBudget $ ExBudget (ExCPU maxInt) (ExMemory maxInt)
                 where maxInt = fromIntegral (maxBound::Int)

-- | 'restricting' instantiated at 'enormousBudget'.
restrictingEnormous :: ST s (ExBudgetMode RestrictingSt uni fun s)
restrictingEnormous = restricting enormousBudget
