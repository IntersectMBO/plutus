{-# LANGUAGE BangPatterns   #-}
{-# LANGUAGE DeriveAnyClass #-}

{-# LANGUAGE StrictData     #-}
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

runCostingFunOneArgument
    :: CostingFun ModelOneArgument
    -> ExMemory
    -> ExBudget
runCostingFunOneArgument (CostingFun cpu mem) =
    let !runCpu = runOneArgumentModel cpu
        !runMem = runOneArgumentModel mem
    in lazy $ \mem1 ->
        ExBudget (ExCPU    $ runCpu mem1)
                 (ExMemory $ runMem mem1)
{-# INLINE runCostingFunOneArgument #-}

runOneArgumentModel
    :: ModelOneArgument
    -> ExMemory
    -> CostingInteger
runOneArgumentModel (ModelOneArgumentConstantCost c) = lazy $ \_ -> c
runOneArgumentModel (ModelOneArgumentLinearCost (ModelLinearSize intercept slope)) = lazy $ \(ExMemory s) ->
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

runCostingFunTwoArguments
    :: CostingFun ModelTwoArguments
    -> ExMemory
    -> ExMemory
    -> ExBudget
runCostingFunTwoArguments (CostingFun cpu mem) =
    let !runCpu = runTwoArgumentModel cpu
        !runMem = runTwoArgumentModel mem
    in lazy $ \mem1 mem2 ->
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
    (ModelTwoArgumentsAddedSizes (ModelAddedSizes intercept slope)) = lazy $ \(ExMemory size1) (ExMemory size2) ->
        (size1 + size2) * slope + intercept -- TODO is this even correct? If not, adjust the other implementations too.
runTwoArgumentModel
    (ModelTwoArgumentsSubtractedSizes (ModelSubtractedSizes intercept slope minSize)) = lazy $ \(ExMemory size1) (ExMemory size2) ->
        (max minSize (size1 - size2)) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsMultipliedSizes (ModelMultipliedSizes intercept slope)) = lazy $ \(ExMemory size1) (ExMemory size2) ->
        (size1 * size2) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsMinSize (ModelMinSize intercept slope)) = lazy $ \(ExMemory size1) (ExMemory size2) ->
        (min size1 size2) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsMaxSize (ModelMaxSize intercept slope)) = lazy $ \(ExMemory size1) (ExMemory size2) ->
        (max size1 size2) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsLinearInX (ModelLinearSize intercept slope)) = lazy $ \(ExMemory size1) (ExMemory _) ->
        size1 * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsLinearInY (ModelLinearSize intercept slope)) = lazy $ \(ExMemory _) (ExMemory size2) ->
        size2 * slope + intercept
runTwoArgumentModel  -- Off the diagonal, return the constant.  On the diagonal, run the one-variable linear model.
    (ModelTwoArgumentsLinearOnDiagonal (ModelConstantOrLinear c intercept slope)) = lazy $ \(ExMemory xSize) (ExMemory ySize) ->
        if xSize == ySize
        then xSize * slope + intercept
        else c
runTwoArgumentModel -- Below the diagonal, return the constant. Above the diagonal, run the other model.
    (ModelTwoArgumentsConstBelowDiagonal (ModelConstantOrTwoArguments c m)) =
        let !run = runTwoArgumentModel m
        in lazy $ \xMem yMem ->
            if xMem > yMem
            then c
            else run xMem yMem
runTwoArgumentModel -- Above the diagonal, return the constant. Below the diagonal, run the other model.
    (ModelTwoArgumentsConstAboveDiagonal (ModelConstantOrTwoArguments c m)) =
        let !run = runTwoArgumentModel m
        in lazy $ \xMem yMem ->
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
runThreeArgumentModel (ModelThreeArgumentsAddedSizes (ModelAddedSizes intercept slope)) = lazy $ \(ExMemory size1) (ExMemory size2) (ExMemory size3) -> lazy $
    (size1 + size2 + size3) * slope + intercept
runThreeArgumentModel (ModelThreeArgumentsLinearInX (ModelLinearSize intercept slope)) = lazy $ \(ExMemory size1) _ _ -> lazy $
    size1 * slope + intercept
runThreeArgumentModel (ModelThreeArgumentsLinearInY (ModelLinearSize intercept slope)) = lazy $ \_ (ExMemory size2) _ -> lazy $
    size2 * slope + intercept
runThreeArgumentModel (ModelThreeArgumentsLinearInZ (ModelLinearSize intercept slope)) = lazy $ \_ _ (ExMemory size3) -> lazy $
    size3 * slope + intercept
{-# NOINLINE runThreeArgumentModel #-}

runCostingFunThreeArguments
    :: CostingFun ModelThreeArguments
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExBudget
runCostingFunThreeArguments (CostingFun cpu mem) =
    let !runCpu = runThreeArgumentModel cpu
        !runMem = runThreeArgumentModel mem
    in lazy $ \mem1 mem2 mem3 ->
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

runCostingFunFourArguments
    :: CostingFun ModelFourArguments
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExBudget
runCostingFunFourArguments (CostingFun cpu mem) =
    let !runCpu = runFourArgumentModel cpu
        !runMem = runFourArgumentModel mem
    in lazy $ \mem1 mem2 mem3 mem4 ->
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

runCostingFunFiveArguments
    :: CostingFun ModelFiveArguments
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExBudget
runCostingFunFiveArguments (CostingFun cpu mem) =
    let !runCpu = runFiveArgumentModel cpu
        !runMem = runFiveArgumentModel mem
    in lazy $ \mem1 mem2 mem3 mem4 mem5 ->
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

runCostingFunSixArguments
    :: CostingFun ModelSixArguments
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExBudget
runCostingFunSixArguments (CostingFun cpu mem) =
    let !runCpu = runSixArgumentModel cpu
        !runMem = runSixArgumentModel mem
    in lazy $ \mem1 mem2 mem3 mem4 mem5 mem6 ->
        ExBudget (ExCPU    $ runCpu mem1 mem2 mem3 mem4 mem5 mem6)
                 (ExMemory $ runMem mem1 mem2 mem3 mem4 mem5 mem6)
{-# INLINE runCostingFunSixArguments #-}
