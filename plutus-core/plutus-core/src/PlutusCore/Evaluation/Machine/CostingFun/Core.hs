-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# LANGUAGE StrictData            #-}
module PlutusCore.Evaluation.Machine.CostingFun.Core
    ( CostingFun(..)
    , ModelAddedSizes(..)
    , ModelSubtractedSizes(..)
    , ModelConstantOrLinear(..)
    , ModelConstantOrTwoArguments(..)
    , ModelLinearSize(..)
    , ModelMultipliedSizes(..)
    , ModelMinSize(..)
    , ModelMaxSize(..)
    , ModelOneArgument(..)
    , ModelTwoArguments(..)
    , ModelThreeArguments(..)
    , ModelFourArguments(..)
    , ModelFiveArguments(..)
    , ModelSixArguments(..)
    , runCostingFunOneArgument
    , runCostingFunTwoArguments
    , runCostingFunThreeArguments
    , runCostingFunFourArguments
    , runCostingFunFiveArguments
    , runCostingFunSixArguments
    , Hashable
    )
where

import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExMemory

import Control.DeepSeq
import Data.Default.Class
import Data.Hashable
import Deriving.Aeson
import GHC.Exts
import Language.Haskell.TH.Syntax hiding (Name, newName)

-- | A class used for convenience in this module, don't export it.
class OnMemoryUsages c a where
    -- | Turn
    --
    -- > \mem1 ... memN -> f mem1 ... memN
    --
    -- into
    --
    -- > \arg1 ... argN -> f (memoryUsage arg1) ... (memoryUsage argN)
    --
    -- so that we don't need to repeat those 'memoryUsage' calls at every use site, which would also
    -- require binding @arg*@ explicitly, i.e. require even more boilerplate.
    onMemoryUsages :: c -> a

instance (ab ~ (a -> b), ExMemoryUsage a, OnMemoryUsages c b) =>
        OnMemoryUsages (ExMemory -> c) ab where
    -- | 'inline' is for making sure that 'memoryUsage' does get inlined.
    onMemoryUsages f = onMemoryUsages . f . inline memoryUsage
    {-# INLINE onMemoryUsages #-}

instance ab ~ ExBudget => OnMemoryUsages ExBudget ab where
    onMemoryUsages = id
    {-# INLINE onMemoryUsages #-}

data CostingFun model = CostingFun
    { costingFunCpu    :: model
    , costingFunMemory :: model
    }
    deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (Default, NFData)

---------------- One-argument costing functions ----------------

data ModelOneArgument =
    ModelOneArgumentConstantCost CostingInteger
    | ModelOneArgumentLinearCost ModelLinearSize
    deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)
instance Default ModelOneArgument where
    def = ModelOneArgumentConstantCost 0

{- Note [runCostingFun* API]
Costing functions take unlifted values, compute the 'ExMemory' of each of them and then invoke
the corresponding @run*Model@ over the computed 'ExMemory's. The reason why we don't just make the
costing functions take 'ExMemory's in the first place is that this would move the burden of
computing the 'ExMemory's onto the caller, i.e. the user defining the meaning of a builtin and it
would be just another hoop to jump through and a completely unnecessary complication for the user.

The reason why costing functions take unlifted values are:

1. we need to unlift them anyway to compute the result of a builtin application, so since we already
   need them elsewhere, we can utilize them in the costing machinery too. Otherwise the costing
   machinery would need to do some unlifting itself, which would be wasteful
2. the costing function might actually depend on the constants that get fed to the builtin.
   For example, checking equality of integers stored in a 'Data' object potentially has a different
   complexity to checking equality of lists of bytestrings
-}

{- Note [Optimizations of runCostingFun*]
We optimize all @runCostingFun*@ functions in the same way:

1. the two calls to @run*Model@ are placed right after matching on the first argument, so that
   they are partially computed and cached, which results in them being called only once per builtin
2. we use a strict case-expression for matching, which GHC can't move inside the resulting lambda
   (unlike a strict let-expression for example)
3. the whole definition is marked with @INLINE@, because it gets worker-wrapper transformed and we
   don't want to keep the worker separate from the wrapper as it just results in unnecessary
   wrapping-unwrapping

In order for @run*Model@ functions to be able to partially compute we need to define them
accordingly, i.e. by matching on the first argument and returning a lambda. We wrap one of the
clauses with a call to 'lazy', so that GHC does not "optimize" the function by moving matching to
the inside of the resulting lambda (which would defeat the whole purpose of caching the function).
It's enough to put 'lazy' in only one of the clauses for all of them to be compiled the right way.
We consistently choose the @*ConstantCost@ clause, because it doesn't need to be optimized anyway
and so a call to 'lazy' doesn't hurt there.

Alternatively, we could use @-fpedantic-bottoms@, which prevents GHC from moving matching above
a lambda (see https://github.com/input-output-hk/plutus/pull/4621), however it doesn't make anything
faster, generates more Core and doesn't take much to break, hence we choose the hacky 'lazy'
version.

Since we want @run*Model@ functions to partially compute, we mark them as @NOINLINE@ to prevent GHC
from inlining them and breaking the sharing friendliness. Without the @NOINLINE@ Core doesn't seem
to be worse, however it was verified that no @NOINLINE@ causes a slowdown in both the @validation@
and @nofib@ benchmarks.

Note that looking at the generated Core isn't really enough. We might have enemies down the pipeline,
for example @-fstg-lift-lams@ looks suspicious:

> Enables the late lambda lifting optimisation on the STG intermediate language. This selectively
> lifts local functions to top-level by converting free variables into function parameters.

This wasn't investigated.

These optimizations gave us a ~3.2% speedup at the time this Note was written.
-}

-- See Note [runCostingFun* API].
runCostingFunOneArgument
    :: ExMemoryUsage a1
    => CostingFun ModelOneArgument
    -> a1
    -> ExBudget
runCostingFunOneArgument (CostingFun cpu mem) =
    case (runOneArgumentModel cpu, runOneArgumentModel mem) of
        (!runCpu, !runMem) -> onMemoryUsages $ \mem1 ->
            ExBudget (ExCPU    $ runCpu mem1)
                     (ExMemory $ runMem mem1)
{-# INLINE runCostingFunOneArgument #-}

runOneArgumentModel
    :: ModelOneArgument
    -> ExMemory
    -> CostingInteger
runOneArgumentModel (ModelOneArgumentConstantCost c) = lazy $ \_ -> c
runOneArgumentModel (ModelOneArgumentLinearCost (ModelLinearSize intercept slope)) = \(ExMemory s) ->
    s * slope + intercept
{-# NOINLINE runOneArgumentModel #-}

---------------- Two-argument costing functions ----------------

-- | s * (x + y) + I
data ModelAddedSizes = ModelAddedSizes
    { modelAddedSizesIntercept :: CostingInteger
    , modelAddedSizesSlope     :: CostingInteger
    } deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

-- | s * (x - y) + I
data ModelSubtractedSizes = ModelSubtractedSizes
    { modelSubtractedSizesIntercept :: CostingInteger
    , modelSubtractedSizesSlope     :: CostingInteger
    , modelSubtractedSizesMinimum   :: CostingInteger
    } deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

data ModelLinearSize = ModelLinearSize
    { modelLinearSizeIntercept :: CostingInteger
    , modelLinearSizeSlope     :: CostingInteger
    } deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

-- | s * (x * y) + I
data ModelMultipliedSizes = ModelMultipliedSizes
    { modelMultipliedSizesIntercept :: CostingInteger
    , modelMultipliedSizesSlope     :: CostingInteger
    } deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

-- | s * min(x, y) + I
data ModelMinSize = ModelMinSize
    { modelMinSizeIntercept :: CostingInteger
    , modelMinSizeSlope     :: CostingInteger
    } deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

-- | s * max(x, y) + I
data ModelMaxSize = ModelMaxSize
    { modelMaxSizeIntercept :: CostingInteger
    , modelMaxSizeSlope     :: CostingInteger
    } deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

-- | if p then s*x else c; p depends on usage
data ModelConstantOrLinear = ModelConstantOrLinear
    { modelConstantOrLinearConstant  :: CostingInteger
    , modelConstantOrLinearIntercept :: CostingInteger
    , modelConstantOrLinearSlope     :: CostingInteger
    } deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

-- | if p then f(x,y) else c; p depends on usage
data ModelConstantOrTwoArguments = ModelConstantOrTwoArguments
    { modelConstantOrTwoArgumentsConstant :: CostingInteger
    , modelConstantOrTwoArgumentsModel    :: ModelTwoArguments
    } deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)


data ModelTwoArguments =
    ModelTwoArgumentsConstantCost       CostingInteger
  | ModelTwoArgumentsLinearInX          ModelLinearSize
  | ModelTwoArgumentsLinearInY          ModelLinearSize
  | ModelTwoArgumentsAddedSizes         ModelAddedSizes
  | ModelTwoArgumentsSubtractedSizes    ModelSubtractedSizes
  | ModelTwoArgumentsMultipliedSizes    ModelMultipliedSizes
  | ModelTwoArgumentsMinSize            ModelMinSize
  | ModelTwoArgumentsMaxSize            ModelMaxSize
  | ModelTwoArgumentsLinearOnDiagonal   ModelConstantOrLinear
  | ModelTwoArgumentsConstAboveDiagonal ModelConstantOrTwoArguments
  | ModelTwoArgumentsConstBelowDiagonal ModelConstantOrTwoArguments
    deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

instance Default ModelTwoArguments where
    def = ModelTwoArgumentsConstantCost 0

-- See Note [runCostingFun* API].
runCostingFunTwoArguments
    :: ( ExMemoryUsage a1
       , ExMemoryUsage a2
       )
    => CostingFun ModelTwoArguments
    -> a1
    -> a2
    -> ExBudget
runCostingFunTwoArguments (CostingFun cpu mem) =
    case (runTwoArgumentModel cpu, runTwoArgumentModel mem) of
        (!runCpu, !runMem) -> onMemoryUsages $ \mem1 mem2 ->
            ExBudget (ExCPU    $ runCpu mem1 mem2)
                     (ExMemory $ runMem mem1 mem2)
{-# INLINE runCostingFunTwoArguments #-}

runTwoArgumentModel
    :: ModelTwoArguments
    -> ExMemory
    -> ExMemory
    -> CostingInteger
runTwoArgumentModel
    (ModelTwoArgumentsConstantCost c) = lazy $ \_ _ -> c
runTwoArgumentModel
    (ModelTwoArgumentsAddedSizes (ModelAddedSizes intercept slope)) = \(ExMemory size1) (ExMemory size2) ->
        (size1 + size2) * slope + intercept -- TODO is this even correct? If not, adjust the other implementations too.
runTwoArgumentModel
    (ModelTwoArgumentsSubtractedSizes (ModelSubtractedSizes intercept slope minSize)) = \(ExMemory size1) (ExMemory size2) ->
        (max minSize (size1 - size2)) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsMultipliedSizes (ModelMultipliedSizes intercept slope)) = \(ExMemory size1) (ExMemory size2) ->
        (size1 * size2) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsMinSize (ModelMinSize intercept slope)) = \(ExMemory size1) (ExMemory size2) ->
        (min size1 size2) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsMaxSize (ModelMaxSize intercept slope)) = \(ExMemory size1) (ExMemory size2) ->
        (max size1 size2) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsLinearInX (ModelLinearSize intercept slope)) = \(ExMemory size1) (ExMemory _) ->
        size1 * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsLinearInY (ModelLinearSize intercept slope)) = \(ExMemory _) (ExMemory size2) ->
        size2 * slope + intercept
runTwoArgumentModel  -- Off the diagonal, return the constant.  On the diagonal, run the one-variable linear model.
    (ModelTwoArgumentsLinearOnDiagonal (ModelConstantOrLinear c intercept slope)) = \(ExMemory xSize) (ExMemory ySize) ->
        if xSize == ySize
        then xSize * slope + intercept
        else c
runTwoArgumentModel -- Below the diagonal, return the constant. Above the diagonal, run the other model.
    (ModelTwoArgumentsConstBelowDiagonal (ModelConstantOrTwoArguments c m)) =
        case runTwoArgumentModel m of
            !run -> \xMem yMem ->
                if xMem > yMem
                then c
                else run xMem yMem
runTwoArgumentModel -- Above the diagonal, return the constant. Below the diagonal, run the other model.
    (ModelTwoArgumentsConstAboveDiagonal (ModelConstantOrTwoArguments c m)) =
        case runTwoArgumentModel m of
            !run -> \xMem yMem ->
                if xMem < yMem
                then c
                else run xMem yMem
{-# NOINLINE runTwoArgumentModel #-}


---------------- Three-argument costing functions ----------------

data ModelThreeArguments =
    ModelThreeArgumentsConstantCost CostingInteger
  | ModelThreeArgumentsAddedSizes   ModelAddedSizes
  | ModelThreeArgumentsLinearInX    ModelLinearSize
  | ModelThreeArgumentsLinearInY    ModelLinearSize
  | ModelThreeArgumentsLinearInZ    ModelLinearSize
    deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

instance Default ModelThreeArguments where
    def = ModelThreeArgumentsConstantCost 0

runThreeArgumentModel
    :: ModelThreeArguments
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> CostingInteger
runThreeArgumentModel (ModelThreeArgumentsConstantCost c) = lazy $ \_ _ _ -> c
runThreeArgumentModel (ModelThreeArgumentsAddedSizes (ModelAddedSizes intercept slope)) = \(ExMemory size1) (ExMemory size2) (ExMemory size3) ->
    (size1 + size2 + size3) * slope + intercept
runThreeArgumentModel (ModelThreeArgumentsLinearInX (ModelLinearSize intercept slope)) = \(ExMemory size1) _ _ ->
    size1 * slope + intercept
runThreeArgumentModel (ModelThreeArgumentsLinearInY (ModelLinearSize intercept slope)) = \_ (ExMemory size2) _ ->
    size2 * slope + intercept
runThreeArgumentModel (ModelThreeArgumentsLinearInZ (ModelLinearSize intercept slope)) = \_ _ (ExMemory size3) ->
    size3 * slope + intercept
{-# NOINLINE runThreeArgumentModel #-}

-- See Note [runCostingFun* API].
runCostingFunThreeArguments
    :: ( ExMemoryUsage a1
       , ExMemoryUsage a2
       , ExMemoryUsage a3
       )
    => CostingFun ModelThreeArguments
    -> a1
    -> a2
    -> a3
    -> ExBudget
runCostingFunThreeArguments (CostingFun cpu mem) =
    case (runThreeArgumentModel cpu, runThreeArgumentModel mem) of
        (!runCpu, !runMem) -> onMemoryUsages $ \mem1 mem2 mem3 ->
            ExBudget (ExCPU    $ runCpu mem1 mem2 mem3)
                     (ExMemory $ runMem mem1 mem2 mem3)
{-# INLINE runCostingFunThreeArguments #-}


---------------- Four-argument costing functions ----------------

data ModelFourArguments =
      ModelFourArgumentsConstantCost CostingInteger
    deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

instance Default ModelFourArguments where
    def = ModelFourArgumentsConstantCost 0

runFourArgumentModel
    :: ModelFourArguments
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> CostingInteger
runFourArgumentModel (ModelFourArgumentsConstantCost c) = lazy $ \_ _ _ _ -> c
{-# NOINLINE runFourArgumentModel #-}

-- See Note [runCostingFun* API].
runCostingFunFourArguments
    :: ( ExMemoryUsage a1
       , ExMemoryUsage a2
       , ExMemoryUsage a3
       , ExMemoryUsage a4
       )
    => CostingFun ModelFourArguments
    -> a1
    -> a2
    -> a3
    -> a4
    -> ExBudget
runCostingFunFourArguments (CostingFun cpu mem) =
    case (runFourArgumentModel cpu, runFourArgumentModel mem) of
        (!runCpu, !runMem) -> onMemoryUsages $ \mem1 mem2 mem3 mem4 ->
            ExBudget (ExCPU    $ runCpu mem1 mem2 mem3 mem4)
                     (ExMemory $ runMem mem1 mem2 mem3 mem4)
{-# INLINE runCostingFunFourArguments #-}


---------------- Five-argument costing functions ----------------

data ModelFiveArguments =
      ModelFiveArgumentsConstantCost CostingInteger
    deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

instance Default ModelFiveArguments where
    def = ModelFiveArgumentsConstantCost 0

runFiveArgumentModel
    :: ModelFiveArguments
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> CostingInteger
runFiveArgumentModel (ModelFiveArgumentsConstantCost c) = lazy $ \_ _ _ _ _ -> c
{-# NOINLINE runFiveArgumentModel #-}

-- See Note [runCostingFun* API].
runCostingFunFiveArguments
    :: ( ExMemoryUsage a1
       , ExMemoryUsage a2
       , ExMemoryUsage a3
       , ExMemoryUsage a4
       , ExMemoryUsage a5
       )
    => CostingFun ModelFiveArguments
    -> a1
    -> a2
    -> a3
    -> a4
    -> a5
    -> ExBudget
runCostingFunFiveArguments (CostingFun cpu mem) =
    case (runFiveArgumentModel cpu, runFiveArgumentModel mem) of
        (!runCpu, !runMem) -> onMemoryUsages $ \mem1 mem2 mem3 mem4 mem5 ->
            ExBudget (ExCPU    $ runCpu mem1 mem2 mem3 mem4 mem5)
                     (ExMemory $ runMem mem1 mem2 mem3 mem4 mem5)
{-# INLINE runCostingFunFiveArguments #-}

---------------- Six-argument costing functions ----------------

data ModelSixArguments =
      ModelSixArgumentsConstantCost CostingInteger
    deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

instance Default ModelSixArguments where
    def = ModelSixArgumentsConstantCost 0

runSixArgumentModel
    :: ModelSixArguments
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> CostingInteger
runSixArgumentModel (ModelSixArgumentsConstantCost c) = lazy $ \_ _ _ _ _ _ -> c
{-# NOINLINE runSixArgumentModel #-}

-- See Note [runCostingFun* API].
runCostingFunSixArguments
    :: ( ExMemoryUsage a1
       , ExMemoryUsage a2
       , ExMemoryUsage a3
       , ExMemoryUsage a4
       , ExMemoryUsage a5
       , ExMemoryUsage a6
       )
    => CostingFun ModelSixArguments
    -> a1
    -> a2
    -> a3
    -> a4
    -> a5
    -> a6
    -> ExBudget
runCostingFunSixArguments (CostingFun cpu mem) =
    case (runSixArgumentModel cpu, runSixArgumentModel mem) of
        (!runCpu, !runMem) -> onMemoryUsages $ \mem1 mem2 mem3 mem4 mem5 mem6 ->
            ExBudget (ExCPU    $ runCpu mem1 mem2 mem3 mem4 mem5 mem6)
                     (ExMemory $ runMem mem1 mem2 mem3 mem4 mem5 mem6)
{-# INLINE runCostingFunSixArguments #-}
