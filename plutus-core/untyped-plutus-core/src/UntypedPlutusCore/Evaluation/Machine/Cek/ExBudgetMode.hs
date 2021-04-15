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
    :: Monoid cost => (ExBudgetCategory fun -> ExBudget -> cost) -> ExBudgetMode cost uni fun
monoidalBudgeting toCost = ExBudgetMode $ do
    costRef <- newSTRef mempty
    let spend key budgetToSpend = liftCekST $ modifySTRef' costRef (<> toCost key budgetToSpend)
    pure . ExBudgetInfo (CekBudgetSpender spend) $ readSTRef costRef

-- | For calculating the cost of execution by counting up using the 'Monoid' instance of 'ExBudget'.
newtype CountingSt = CountingSt ExBudget
    deriving stock (Eq, Show)
    deriving newtype (Semigroup, Monoid, PrettyBy config, NFData)

instance Pretty CountingSt where
    pretty (CountingSt budget) = parens $ "required budget:" <+> pretty budget <> line

-- | For calculating the cost of execution.
counting :: ExBudgetMode CountingSt uni fun
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
tallying :: (Eq fun, Hashable fun) => ExBudgetMode (TallyingSt fun) uni fun
tallying =
    monoidalBudgeting $ \key budgetToSpend ->
        TallyingSt (CekExTally $ singleton key budgetToSpend) budgetToSpend

newtype RestrictingSt = RestrictingSt ExRestrictingBudget
    deriving stock (Eq, Show)
    deriving newtype (NFData)
    deriving anyclass (PrettyBy config)

instance Pretty RestrictingSt where
    pretty (RestrictingSt budget) = parens $ "final budget:" <+> pretty budget <> line

-- | For execution, to avoid overruns.
restricting :: ExRestrictingBudget -> ExBudgetMode RestrictingSt uni fun
restricting (ExRestrictingBudget (ExBudget cpuInit memInit)) = ExBudgetMode $ do
    -- Using two separate 'STRef's instead of a single one for efficiency reasons.
    -- Gave us a ~1% speedup the time this idea was implemented.
    cpuRef <- newSTRef cpuInit
    memRef <- newSTRef memInit
    let spend _ (ExBudget cpuToSpend memToSpend) = do
            cpuLeft <- liftCekST $ readSTRef cpuRef
            memLeft <- liftCekST $ readSTRef memRef
            let cpuLeft' = cpuLeft `minusExCPU` cpuToSpend
            let memLeft' = memLeft `minusExMemory` memToSpend
            -- Note that even if we throw an out-of-budget error, we still need to record
            -- what the final state was.
            liftCekST . writeSTRef cpuRef $! cpuLeft'
            liftCekST . writeSTRef memRef $! memLeft'
            when (cpuLeft' < 0 || memLeft' < 0) $
                throwingWithCause _EvaluationError
                    (UserEvaluationError . CekOutOfExError $
                        ExRestrictingBudget $ ExBudget cpuLeft' memLeft')
                    Nothing
    pure . ExBudgetInfo (CekBudgetSpender spend) $ do
        finalExBudget <- ExBudget <$> readSTRef cpuRef <*> readSTRef memRef
        pure . RestrictingSt $ ExRestrictingBudget finalExBudget

-- | When we want to just evaluate the program we use the 'Restricting' mode with an enormous
-- budget, so that evaluation costs of on-chain budgeting are reflected accurately in benchmarks.
enormousBudget :: ExRestrictingBudget
enormousBudget = ExRestrictingBudget $ ExBudget (ExCPU maxInt) (ExMemory maxInt)
                 where maxInt = fromIntegral (maxBound::Int)

-- | 'restricting' instantiated at 'enormousBudget'.
restrictingEnormous :: ExBudgetMode RestrictingSt uni fun
restrictingEnormous = restricting enormousBudget
