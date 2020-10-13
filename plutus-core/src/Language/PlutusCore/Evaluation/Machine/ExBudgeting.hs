{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE QuasiQuotes            #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

{- Note [Budgeting]

When running Plutus code on the chain, you're running code on other peoples
machines, so you'll have to pay for it. And it has to be possible to determine
how much money that should be before sending the transaction with the Plutus
code to the chain. If you spend too little, your transaction will be rejected.
If you spend too much, you're wasting money. So it must be possible to estimate
how much a script will cost. The easiest way to do so is to run the script
locally and determine the cost. The functional nature of Plutus allows for the
assumption it will cost a similar amount locally as on the chain. See
'CekBudgetMode'.

Additionally, it's helpful to know which parts of the script cost how much. We
assume it's useful to have a list of costs per term executed, so it's possible
to estimate which parts of the script cost how much. The 'ExTally' has not been
determined to be useful, but it was easy to implement.

We're tracking execution cost via both memory (via 'ExMemory') and CPU (via
'ExCPU'). Node operators are more interested in space limits than time limits -
the memory upper limit will be reached faster than the time limit (which would
be until next block). The two resources are then converted to the main currency
of the chain based on protocol parameters - that way it's possible to adjust the
actual fees without changing the code.

When tracking memory, we ignore garbage collection - only total memory
allocation is counted. This decision decouples us from the implementation of the
GC itself. Additionally, sharing of references is assumed. If a builtin
generates a new value, every reference of that value (e.g. in different CEK
environments) is assumed to point to the same value, without any copies. So the
total memory of the program is bounded to the original program + anything the
builtins produce + the machine space used by the CEK machine itself. The CEK
environment costs are included in the stack frame costs of the CEK machine,
they're linear.

The tracking of the costs themselves does not cost any CPU or memory. Currently
that's an implementation detail. We may have to readjust this depending on real
world experience.

The CEK machine does budgeting in these steps:
- The memory cost of the initial AST is added to the budget. See Note [Memory
  Usage for Plutus]. This operation currently does not cost any CPU. It
  currently costs as much memory as the AST itself, before aborting. See
  https://github.com/input-output-hk/plutus/issues/1799 for more discussion.
- Then each machine reduction step requires a certain amount of memory and CPU.
- The builtin operations may require different amounts of memory and CPU,
  depending on the input size.
- If a computation runs out of Memory or CPU, it is aborted, via the same
  mechanism when 'error' is called.

Tracking CEK machine layers is rather straightforward, albeit these numbers
still have to be filled in. For builtins (e.g. +, etc.) the cost tracking can be
a bit more complicated, as the required resources may depend on the size of the
inputs (E.g. multiplying numbers, where the output will be around 6 words if
both inputs are at 3 words each). These cost estimations will also have factors
attached which can be configured at runtime via protocol parameters - so it's
possible to adjust them at runtime.

-}

module Language.PlutusCore.Evaluation.Machine.ExBudgeting
    ( ExBudgetMode(..)
    , ExBudget(..)
    , ExBudgetState(..)
    , ExTally(..)
    , ExRestrictingBudget(..)
    , ToExMemory(..)
    , ExBudgetBuiltin(..)
    , SpendBudget(..)
    , CostModel
    , CostModelBase(..)
    , CostingFun(..)
    , ModelAddedSizes(..)
    , ModelSubtractedSizes(..)
    , ModelOrientation(..)
    , ModelLinearSize(..)
    , ModelMultiSizes(..)
    , ModelMinSize(..)
    , ModelMaxSize(..)
    , ModelSplitConst(..)
    , ModelOneArgument(..)
    , ModelTwoArguments(..)
    , ModelThreeArguments(..)
    , exBudgetCPU
    , exBudgetMemory
    , exBudgetStateBudget
    , exBudgetStateTally
    , exceedsBudget
    , runCostingFunOneArgument
    , runCostingFunTwoArguments
    , runCostingFunThreeArguments
    , Hashable
    )
where


import           Language.PlutusCore.Core
import           Language.PlutusCore.Name
import           PlutusPrelude

import           Barbies
import           Control.Lens.Indexed
import           Control.Lens.TH                                 (makeLenses)
import           Data.Default.Class
import           Data.Hashable
import           Data.HashMap.Monoidal
import qualified Data.Kind                                       as Kind
import           Data.List                                       (intersperse)
import           Data.Semigroup.Generic
import           Data.Text.Prettyprint.Doc
import           Deriving.Aeson
import           Language.Haskell.TH.Syntax                      hiding (Name)
import           Language.PlutusCore.Evaluation.Machine.ExMemory

newtype ExRestrictingBudget = ExRestrictingBudget ExBudget deriving (Show, Eq)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid ExBudget)

data ExBudgetMode =
      Counting -- ^ For precalculation
    | Restricting ExRestrictingBudget -- ^ For execution, to avoid overruns

class ToExMemory term where
    -- | Get the 'ExMemory' of a @term@. If the @term@ is not annotated with 'ExMemory', then
    -- return something arbitrary just to fit such a term into the builtin application machinery.
    toExMemory :: term -> ExMemory

instance ToExMemory (Term TyName Name uni fun ()) where
    toExMemory _ = 0

instance ToExMemory (Term TyName Name uni fun ExMemory) where
    toExMemory = termAnn

-- | A class for injecting a 'Builtin' into an @exBudgetCat@.
-- We need it, because the constant application machinery calls 'spendBudget' before reducing a
-- constant application and we want to be general over @exBudgetCat@ there, but still track the
-- built-in functions category, hence the ad hoc polymorphism.
class ExBudgetBuiltin fun exBudgetCat where
    exBudgetBuiltin :: fun -> exBudgetCat

-- | A dummy 'ExBudgetBuiltin' instance to be used in monads where we don't care about costing.
instance ExBudgetBuiltin fun () where
    exBudgetBuiltin _ = ()

-- This works nicely because @m@ contains @term@.
class (ExBudgetBuiltin fun exBudgetCat, ToExMemory term) =>
            SpendBudget m fun exBudgetCat term | m -> fun exBudgetCat term where
    -- | Spend the budget, which may mean different things depending on the monad:
    --
    -- 1. do nothing for an evaluator that does not care about costing
    -- 2. count upwards to get the cost of a computation
    -- 3. subtract from the current budget and fail if the budget goes below zero
    spendBudget :: exBudgetCat -> ExBudget -> m ()

data ExBudget = ExBudget { _exBudgetCPU :: ExCPU, _exBudgetMemory :: ExMemory }
    deriving stock (Eq, Show, Generic)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid ExBudget)
    deriving anyclass NFData
instance PrettyDefaultBy config Integer => PrettyBy config ExBudget where
    prettyBy config (ExBudget cpu memory) = parens $ fold
        [ "{ cpu: ", prettyBy config cpu, line
        , "| mem: ", prettyBy config memory, line
        , "}"
        ]

data ExBudgetState  exBudgetCat = ExBudgetState
    { _exBudgetStateTally  :: ExTally exBudgetCat -- ^ for counting what cost how much
    , _exBudgetStateBudget :: ExBudget -- ^ for making sure we don't spend too much
    }
    deriving stock (Eq, Generic, Show)
    deriving anyclass NFData
instance ( PrettyDefaultBy config Integer, PrettyBy config exBudgetCat
         , Eq exBudgetCat, Hashable exBudgetCat
         ) => PrettyBy config (ExBudgetState exBudgetCat) where
    prettyBy config (ExBudgetState tally budget) = parens $ fold
        [ "{ tally: ", prettyBy config tally, line
        , "| budget: ", prettyBy config budget, line
        , "}"
        ]

newtype ExTally exBudgetCat = ExTally (MonoidalHashMap exBudgetCat ExBudget)
    deriving stock (Eq, Generic, Show)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid (ExTally exBudgetCat))
    deriving anyclass NFData
instance ( PrettyDefaultBy config Integer, PrettyBy config exBudgetCat
         , Eq exBudgetCat, Hashable exBudgetCat
         ) => PrettyBy config (ExTally exBudgetCat) where
    prettyBy config (ExTally m) =
        parens $ fold (["{ "] <> (intersperse (line <> "| ") $ fmap group $
          ifoldMap (\k v -> [(prettyBy config k <+> "causes" <+> prettyBy config v)]) m) <> ["}"])

type CostModel = CostModelBase CostingFun

-- | The main model which contains all data required to predict the cost of builtin functions. See Note [Creation of the Cost Model] for how this is generated. Calibrated for the CeK machine.
data CostModelBase f =
    CostModel
    { paramAddInteger           :: f ModelTwoArguments
    , paramSubtractInteger      :: f ModelTwoArguments
    , paramMultiplyInteger      :: f ModelTwoArguments
    , paramDivideInteger        :: f ModelTwoArguments
    , paramQuotientInteger      :: f ModelTwoArguments
    , paramRemainderInteger     :: f ModelTwoArguments
    , paramModInteger           :: f ModelTwoArguments
    , paramLessThanInteger      :: f ModelTwoArguments
    , paramLessThanEqInteger    :: f ModelTwoArguments
    , paramGreaterThanInteger   :: f ModelTwoArguments
    , paramGreaterThanEqInteger :: f ModelTwoArguments
    , paramEqInteger            :: f ModelTwoArguments
    , paramConcatenate          :: f ModelTwoArguments
    , paramTakeByteString       :: f ModelTwoArguments -- TODO these two might be a bit interesting on size
    , paramDropByteString       :: f ModelTwoArguments
    , paramSHA2                 :: f ModelOneArgument
    , paramSHA3                 :: f ModelOneArgument
    , paramVerifySignature      :: f ModelThreeArguments
    , paramEqByteString         :: f ModelTwoArguments
    , paramLtByteString         :: f ModelTwoArguments
    , paramGtByteString         :: f ModelTwoArguments
    , paramIfThenElse           :: f ModelThreeArguments
    }
    deriving (Generic, FunctorB, TraversableB, ConstraintsB)

deriving via CustomJSON '[FieldLabelModifier (StripPrefix "param", CamelToSnake)] (CostModelBase CostingFun) instance ToJSON (CostModelBase CostingFun)
deriving via CustomJSON '[FieldLabelModifier (StripPrefix "param", CamelToSnake)] (CostModelBase CostingFun) instance FromJSON (CostModelBase CostingFun)

type AllArgumentModels (constraint :: Kind.Type -> Kind.Constraint) f = (constraint (f ModelOneArgument), constraint (f ModelTwoArguments), constraint (f ModelThreeArguments))

-- HLS doesn't like the AllBF from Barbies.
deriving instance AllArgumentModels NFData f => NFData (CostModelBase f)
deriving instance AllArgumentModels Default f => Default (CostModelBase f)
deriving instance AllArgumentModels Lift f => Lift (CostModelBase f)
deriving instance AllArgumentModels Show f => Show (CostModelBase f)
deriving instance AllArgumentModels Eq f => Eq (CostModelBase f)

-- TODO there's probably a nice way to abstract over the number of arguments here. Feel free to implement it.

data CostingFun model = CostingFun
    { costingFunCpu    :: model
    , costingFunMemory :: model
    }
    deriving (Show, Eq, Generic, Lift, Default, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "costingFun", CamelToSnake)] (CostingFun model)

data ModelOneArgument =
    ModelOneArgumentConstantCost Integer
    | ModelOneArgumentAddedSizes ModelAddedSizes
    deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[SumTaggedObject "type" "arguments", ConstructorTagModifier (StripPrefix "ModelOneArgument", CamelToSnake)] ModelOneArgument
instance Default ModelOneArgument where
    def = ModelOneArgumentConstantCost 1

runCostingFunOneArgument :: CostingFun ModelOneArgument -> ExMemory -> ExBudget
runCostingFunOneArgument
    (CostingFun cpu mem) mem1 =
        ExBudget (ExCPU (runOneArgumentModel cpu mem1)) (ExMemory (runOneArgumentModel mem mem1))

runOneArgumentModel :: ModelOneArgument -> ExMemory -> Integer
runOneArgumentModel (ModelOneArgumentConstantCost i) _ = i
runOneArgumentModel (ModelOneArgumentAddedSizes (ModelAddedSizes intercept slope)) (ExMemory s) = ceiling $ (fromInteger s) * slope + intercept

-- | s * (x + y) + I
data ModelAddedSizes = ModelAddedSizes
    { modelAddedSizesIntercept :: Double
    , modelAddedSizesSlope     :: Double
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelAddedSizes", CamelToSnake)] ModelAddedSizes

-- | s * (x - y) + I
data ModelSubtractedSizes = ModelSubtractedSizes
    { modelSubtractedSizesIntercept :: Double
    , modelSubtractedSizesSlope     :: Double
    , modelSubtractedSizesMinimum   :: Double
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelSubtractedSizes", CamelToSnake)] ModelSubtractedSizes

data ModelOrientation =
    ModelOrientationX
    | ModelOrientationY
    deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[SumTaggedObject "type" "arguments", ConstructorTagModifier (StripPrefix "ModelOrientation", CamelToSnake)] ModelOrientation

data ModelLinearSize = ModelLinearSize
    { modelLinearSizeIntercept   :: Double
    , modelLinearSizeSlope       :: Double
    , modelLinearSizeOrientation :: ModelOrientation -- ^ x or y?
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelLinearSize", CamelToSnake)] ModelLinearSize

-- | s * (x * y) + I
data ModelMultiSizes = ModelMultiSizes
    { modelMultiSizesIntercept :: Double
    , modelMultiSizesSlope     :: Double
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelMultiSizes", CamelToSnake)] ModelMultiSizes

-- | s * min(x, y) + I
data ModelMinSize = ModelMinSize
    { modelMinSizeIntercept :: Double
    , modelMinSizeSlope     :: Double
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelMinSize", CamelToSnake)] ModelMinSize

data ModelMaxSize = ModelMaxSize
    { modelMaxSizeIntercept :: Double
    , modelMaxSizeSlope     :: Double
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelMaxSize", CamelToSnake)] ModelMaxSize

-- | (if (x > y) then s * (x + y) else 0) + I
data ModelSplitConst = ModelSplitConst
    { modelSplitConstIntercept :: Double
    , modelSplitConstSlope     :: Double
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "ModelSplitConst", CamelToSnake)] ModelSplitConst

data ModelTwoArguments =
    ModelTwoArgumentsConstantCost Integer
    | ModelTwoArgumentsAddedSizes ModelAddedSizes
    | ModelTwoArgumentsSubtractedSizes ModelSubtractedSizes
    | ModelTwoArgumentsMultiSizes ModelMultiSizes
    | ModelTwoArgumentsMinSize ModelMinSize
    | ModelTwoArgumentsMaxSize ModelMaxSize
    | ModelTwoArgumentsSplitConstMulti ModelSplitConst
    | ModelTwoArgumentsLinearSize ModelLinearSize
    deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[SumTaggedObject "type" "arguments", ConstructorTagModifier (StripPrefix "ModelTwoArguments", CamelToSnake)] ModelTwoArguments

instance Default ModelTwoArguments where
    def = ModelTwoArgumentsConstantCost 1

runCostingFunTwoArguments :: CostingFun ModelTwoArguments -> ExMemory -> ExMemory -> ExBudget
runCostingFunTwoArguments (CostingFun cpu mem) mem1 mem2 =
    ExBudget (ExCPU (runTwoArgumentModel cpu mem1 mem2)) (ExMemory (runTwoArgumentModel mem mem1 mem2))

runTwoArgumentModel :: ModelTwoArguments -> ExMemory -> ExMemory -> Integer
runTwoArgumentModel
    (ModelTwoArgumentsConstantCost c) _ _ = c
runTwoArgumentModel
    (ModelTwoArgumentsAddedSizes (ModelAddedSizes intercept slope)) (ExMemory size1) (ExMemory size2) =
        ceiling $ (fromInteger (size1 + size2)) * slope + intercept -- TODO is this even correct? If not, adjust the other implementations too.
runTwoArgumentModel
    (ModelTwoArgumentsSubtractedSizes (ModelSubtractedSizes intercept slope minSize)) (ExMemory size1) (ExMemory size2) =
        ceiling $ (max minSize (fromInteger (size1 - size2))) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsMultiSizes (ModelMultiSizes intercept slope)) (ExMemory size1) (ExMemory size2) =
        ceiling $ (fromInteger (size1 * size2)) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsMinSize (ModelMinSize intercept slope)) (ExMemory size1) (ExMemory size2) =
        ceiling $ (fromInteger (min size1 size2)) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsMaxSize (ModelMaxSize intercept slope)) (ExMemory size1) (ExMemory size2) =
        ceiling $ (fromInteger (max size1 size2)) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsSplitConstMulti (ModelSplitConst intercept slope)) (ExMemory size1) (ExMemory size2) =
        ceiling $ (if (size1 > size2) then (fromInteger size1) * (fromInteger size2) else 0) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsLinearSize (ModelLinearSize intercept slope ModelOrientationX)) (ExMemory size1) (ExMemory _) =
        ceiling $ (fromInteger size1) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsLinearSize (ModelLinearSize intercept slope ModelOrientationY)) (ExMemory _) (ExMemory size2) =
        ceiling $ (fromInteger size2) * slope + intercept

data ModelThreeArguments =
    ModelThreeArgumentsConstantCost Integer
  | ModelThreeArgumentsAddedSizes ModelAddedSizes
    deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[SumTaggedObject "type" "arguments", ConstructorTagModifier (StripPrefix "ModelThreeArguments", CamelToSnake)] ModelThreeArguments

instance Default ModelThreeArguments where
    def = ModelThreeArgumentsConstantCost 1

runThreeArgumentModel :: ModelThreeArguments -> ExMemory -> ExMemory -> ExMemory -> Integer
runThreeArgumentModel (ModelThreeArgumentsConstantCost i) _ _ _ = i
runThreeArgumentModel (ModelThreeArgumentsAddedSizes (ModelAddedSizes intercept slope)) (ExMemory size1) (ExMemory size2) (ExMemory size3) =
    ceiling $ (fromInteger (size1 + size2 + size3)) * slope + intercept

runCostingFunThreeArguments :: CostingFun ModelThreeArguments -> ExMemory -> ExMemory -> ExMemory -> ExBudget
runCostingFunThreeArguments (CostingFun cpu mem) mem1 mem2 mem3 =
    ExBudget (ExCPU $ runThreeArgumentModel cpu mem1 mem2 mem3) (ExMemory $ runThreeArgumentModel mem mem1 mem2 mem3)

$(mtraverse makeLenses [''ExBudgetState, ''ExBudget])

exceedsBudget :: ExRestrictingBudget -> ExBudget -> Bool
exceedsBudget (ExRestrictingBudget ex) budget = (view exBudgetCPU budget) > (view exBudgetCPU ex) || (view exBudgetMemory budget) > (view exBudgetMemory ex)
