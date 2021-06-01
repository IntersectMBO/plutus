{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}

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
import           Data.Primitive.PrimArray
import           Data.STRef
import           Data.SatInt
import           Data.Semigroup.Generic
import           Data.Text.Prettyprint.Doc
import           Text.PrettyBy                                     (IgnorePrettyConfig (..))

-- | Construct an 'ExBudgetMode' out of a function returning a value of the budgeting state type.
-- The value then gets added to the current state via @(<>)@.
monoidalBudgeting
    :: Monoid cost => (ExBudgetCategory fun -> ExBudget -> cost) -> ExBudgetMode cost uni fun
monoidalBudgeting toCost = ExBudgetMode $ do
    costRef <- newSTRef mempty
    let spend key budgetToSpend = CekCarryingM $ modifySTRef' costRef (<> toCost key budgetToSpend)
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
restricting :: forall uni fun . (PrettyUni uni fun) => ExRestrictingBudget -> ExBudgetMode RestrictingSt uni fun
restricting (ExRestrictingBudget (ExBudget cpuInit memInit)) = ExBudgetMode $ do
    -- We keep the counters in a PrimArray. This is better than an STRef since it stores its contents unboxed.
    --
    -- If we don't specify the element type then GHC has difficulty inferring it, but it's
    -- annoying to specify the monad, since it refers to the 's' which is not in scope.
    ref <- newPrimArray @_ @SatInt 2
    let
        cpuIx = 0
        memIx = 1
        readCpu = coerce <$> readPrimArray ref cpuIx
        writeCpu cpu = writePrimArray ref cpuIx $ coerce cpu
        readMem = coerce <$> readPrimArray ref memIx
        writeMem mem = writePrimArray ref memIx $ coerce mem

    writeCpu cpuInit
    writeMem memInit
    let
        spend _ (ExBudget cpuToSpend memToSpend) = do
            cpuLeft <- CekCarryingM readCpu
            memLeft <- CekCarryingM readMem
            let cpuLeft' = cpuLeft - cpuToSpend
            let memLeft' = memLeft - memToSpend
            -- Note that even if we throw an out-of-budget error, we still need to record
            -- what the final state was.
            CekCarryingM $ writeCpu cpuLeft'
            CekCarryingM $ writeMem memLeft'
            when (cpuLeft' < 0 || memLeft' < 0) $ do
                let budgetLeft' = ExBudget cpuLeft' memLeft'
                throwingWithCause _EvaluationError
                    (UserEvaluationError . CekOutOfExError $ ExRestrictingBudget budgetLeft')
                    Nothing
    pure . ExBudgetInfo (CekBudgetSpender spend) $ do
        finalExBudget <- ExBudget <$> readCpu <*> readMem
        pure . RestrictingSt $ ExRestrictingBudget finalExBudget

-- | 'restricting' instantiated at 'enormousBudget'.
restrictingEnormous :: (PrettyUni uni fun) => ExBudgetMode RestrictingSt uni fun
restrictingEnormous = restricting enormousBudget
