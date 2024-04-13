-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumericUnderscores    #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# LANGUAGE StrictData            #-}
module PlutusCore.Evaluation.Machine.CostingFun.Core
    ( CostingFun(..)
    , UnimplementedCostingFun(..)
    , Intercept(..)
    , Slope(..)
    , Coefficient0(..)
    , Coefficient1(..)
    , Coefficient2(..)
    , OneVariableLinearFunction(..)
    , TwoVariableLinearFunction(..)
    , OneVariableQuadraticFunction(..)
    , ModelSubtractedSizes(..)
    , ModelConstantOrOneArgument(..)
    , ModelConstantOrTwoArguments(..)
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

import PlutusCore.Evaluation.Machine.CostStream
import PlutusCore.Evaluation.Machine.ExBudgetStream
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Machine.ExMemoryUsage

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
        OnMemoryUsages (CostStream -> c) ab where
    -- 'inline' is for making sure that 'memoryUsage' does get inlined.
    onMemoryUsages f = onMemoryUsages . f . flattenCostRose . inline memoryUsage
    {-# INLINE onMemoryUsages #-}

instance ab ~ ExBudgetStream => OnMemoryUsages ExBudgetStream ab where
    onMemoryUsages = id
    {-# INLINE onMemoryUsages #-}

{- | A type of costing functions parametric over a model type.  In practice the we
have one model type `Model<N>Arguments` for every N, where N is the arity of the
builtin whose costs we want to model.  Each model type has a number of
constructors defining different "shapes" of N-parameter functions which
calculate a cost given the sizes of the builtin's arguments. -}
data CostingFun model = CostingFun
    { costingFunCpu    :: model
    , costingFunMemory :: model
    }
    deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (Default, NFData)

{- | In the initial stages of implementing a new builtin it is necessary to
   provide a temporary costing function which is used until the builtin has been
   properly costed: `see CostModelGeneration.md`.  Each `Model<N>Arguments` type
   defines an instance of this class where `unimplementedCostingFun` is a
   constant costing function which returns a very high cost for all inputs.
   This prevents new functions from being used in situations where costs are
   important until a sensible costing function has been implemented. -}
class UnimplementedCostingFun a where
  unimplementedCostingFun :: b -> CostingFun a

{- | Make a very expensive pair of CPU and memory costing functions.  The name is
   slightly misleading because it actually makes a function which returns such a
   pair, which is what is required at the use site in `PlutusCore.Default.Builtins`,
   where properly implemented costing functions are constructed from a
   BuiltinCostModel object.  We can't use maxBound :: CostingInteger because then the
   evaluator always fails; instead we assign a cost of 100,000,000,000, which is well
   beyond the current on-chain CPU and memory limits (10,000,000,000 and 14,000,000
   respectively) but still allows over 92,000,000 evaluations before the maximum
   CostingInteger is reached.  This allows us to use an "uncosted" builtin for
   testing and for running costing benchmarks, but will prevent it from being used
   when the Plutus Core evaluator is invoked by the ledger.
-}
makeUnimplementedCostingFun :: (CostingInteger -> model) -> b -> CostingFun model
makeUnimplementedCostingFun c =
  const $ CostingFun (c k) (c k)
  where k = 100_000_000_000

---------------- Types for use within costing functions ----------------

-- | A wrapped 'CostingInteger' that is supposed to be used as an intercept.
newtype Intercept = Intercept
    { unIntercept :: CostingInteger
    } deriving stock (Generic, Lift)
      deriving newtype (Show, Eq, Num, NFData)

-- | A wrapped 'CostingInteger' that is supposed to be used as a slope.
newtype Slope = Slope
    { unSlope :: CostingInteger
    } deriving stock (Generic, Lift)
      deriving newtype (Show, Eq, Num, NFData)

-- | A wrapped 'CostingInteger' that is supposed to be used as the degree 0
-- coefficient of a polynomial.
newtype Coefficient0 = Coefficient0
    { unCoefficient0 :: CostingInteger
    } deriving stock (Generic, Lift)
      deriving newtype (Show, Eq, Num, NFData)

-- | A wrapped 'CostingInteger' that is supposed to be used as the degree 1
-- coefficient of a polynomial.
newtype Coefficient1 = Coefficient1
    { unCoefficient1 :: CostingInteger
    } deriving stock (Generic, Lift)
      deriving newtype (Show, Eq, Num, NFData)

-- | A wrapped 'CostingInteger' that is supposed to be used as the degree 2
-- coefficient of a polynomial.
newtype Coefficient2 = Coefficient2
    { unCoefficient2 :: CostingInteger
    } deriving stock (Generic, Lift)
      deriving newtype (Show, Eq, Num, NFData)

---------------- One-argument costing functions ----------------

data ModelOneArgument =
    ModelOneArgumentConstantCost CostingInteger
    | ModelOneArgumentLinearInX OneVariableLinearFunction
    deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

instance Default ModelOneArgument where
    def = ModelOneArgumentConstantCost maxBound

instance UnimplementedCostingFun ModelOneArgument where
  unimplementedCostingFun = makeUnimplementedCostingFun ModelOneArgumentConstantCost

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
It's enough to put 'lazy' in only one of the clauses for all of them to be compiled the right way,
however adding 'lazy' to all the other clauses too turned out to improve performance by a couple of
percent, reasons are unclear.

Alternatively, we could use @-fpedantic-bottoms@, which prevents GHC from moving matching above
a lambda (see https://github.com/IntersectMBO/plutus/pull/4621), however it doesn't make anything
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
    -> ExBudgetStream
runCostingFunOneArgument (CostingFun cpu mem) =
    case (runOneArgumentModel cpu, runOneArgumentModel mem) of
        (!runCpu, !runMem) -> onMemoryUsages $ \mem1 ->
            zipCostStream
                (runCpu mem1)
                (runMem mem1)
{-# INLINE runCostingFunOneArgument #-}

-- | Take an intercept, a slope and a stream and scale each element of the stream by the slope and
-- cons the intercept to the stream afterwards.
scaleLinearly :: Intercept -> Slope -> CostStream -> CostStream
scaleLinearly (Intercept intercept) (Slope slope) =
    addCostStream (CostLast intercept) . mapCostStream (slope *)
{-# INLINE scaleLinearly #-}

runOneArgumentModel
    :: ModelOneArgument
    -> CostStream
    -> CostStream
runOneArgumentModel (ModelOneArgumentConstantCost c) =
    lazy $ \_ -> CostLast c
runOneArgumentModel (ModelOneArgumentLinearInX (OneVariableLinearFunction intercept slope)) =
    lazy $ \costs1 -> scaleLinearly intercept slope costs1
{-# NOINLINE runOneArgumentModel #-}

---------------- Two-argument costing functions ----------------

{- Because of the way the costing code has evolved the names of the model types
below aren't very consistent.  However it's a little difficult to change them
because that would change some of the JSON tags in the cost model file.  The
basic models are one-variable and two-variable linear models and their names
(`OneVariableLinearFunction` and `TwoVariableLinearFunction`) reflect this .
Other models have names like `ModelAddedSizes` and it might be more logical if
they were called things like `LinearInXPlusY` and so on since these are really
abstract functions that don't know anything about sizes.  Also many of the types
have their own intercept and slope values because they are linear on some
function of the inputs or are linear in some region of the plane.  Maybe these
should contain nested objects of type ModelLinearInOneVariable instead, but that
would complicate the JSON encoding and might also impact efficiency.
-}

-- | s * x + I
data OneVariableLinearFunction = OneVariableLinearFunction
    { oneVariableLinearFunctionIntercept :: Intercept
    , oneVariableLinearFunctionSlope     :: Slope
    } deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

-- | s1 * x + s2 * y + I
data TwoVariableLinearFunction = TwoVariableLinearFunction
    { twoVariableLinearFunctionIntercept :: Intercept
    , twoVariableLinearFunctionSlopeX    :: Slope
    , twoVariableLinearFunctionSlopeY    :: Slope
    } deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

-- | c2*x^2 + c1*x + c0
data OneVariableQuadraticFunction = OneVariableQuadraticFunction
    { oneVariableQuadraticFunctionC0 :: Coefficient0
    , oneVariableQuadraticFunctionC1 :: Coefficient1
    , oneVariableQuadraticFunctionC2 :: Coefficient2
    } deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

{-# INLINE evaluateOneVariableQuadraticFunction #-}
evaluateOneVariableQuadraticFunction :: OneVariableQuadraticFunction -> CostingInteger -> CostingInteger
evaluateOneVariableQuadraticFunction
   (OneVariableQuadraticFunction (Coefficient0 c0) (Coefficient1 c1)  (Coefficient2 c2)) x =
       c0 + c1*x + c2*x*x

-- FIXME: we could use ModelConstantOrOneArgument for
-- ModelTwoArgumentsSubtractedSizes instead, but that would change the order of
-- the cost model parameters since the minimum value would come first instead of
-- last.
-- | s * (x - y) + I
data ModelSubtractedSizes = ModelSubtractedSizes
    { modelSubtractedSizesIntercept :: Intercept
    , modelSubtractedSizesSlope     :: Slope
    , modelSubtractedSizesMinimum   :: CostingInteger
    } deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

-- | if p then f(x) else c; p depends on usage
data ModelConstantOrOneArgument = ModelConstantOrOneArgument
    { modelConstantOrOneArgumentConstant :: CostingInteger
    , modelConstantOrOneArgumentModel    :: ModelOneArgument
    } deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

-- | if p then f(x,y) else c; p depends on usage
data ModelConstantOrTwoArguments = ModelConstantOrTwoArguments
    { modelConstantOrTwoArgumentsConstant :: CostingInteger
    , modelConstantOrTwoArgumentsModel    :: ModelTwoArguments
    } deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)


data ModelTwoArguments =
    ModelTwoArgumentsConstantCost        CostingInteger
  | ModelTwoArgumentsLinearInX           OneVariableLinearFunction
  | ModelTwoArgumentsLinearInY           OneVariableLinearFunction
  | ModelTwoArgumentsLinearInXAndY       TwoVariableLinearFunction
  | ModelTwoArgumentsAddedSizes          OneVariableLinearFunction
  | ModelTwoArgumentsSubtractedSizes     ModelSubtractedSizes
  | ModelTwoArgumentsMultipliedSizes     OneVariableLinearFunction
  | ModelTwoArgumentsMinSize             OneVariableLinearFunction
  | ModelTwoArgumentsMaxSize             OneVariableLinearFunction
  | ModelTwoArgumentsConstOffDiagonal    ModelConstantOrOneArgument
  | ModelTwoArgumentsConstAboveDiagonal  ModelConstantOrTwoArguments
  | ModelTwoArgumentsConstBelowDiagonal  ModelConstantOrTwoArguments
  | ModelTwoArgumentsQuadraticInY        OneVariableQuadraticFunction
    deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

instance Default ModelTwoArguments where
    def = ModelTwoArgumentsConstantCost maxBound

instance UnimplementedCostingFun ModelTwoArguments where
  unimplementedCostingFun = makeUnimplementedCostingFun ModelTwoArgumentsConstantCost

-- See Note [runCostingFun* API].
runCostingFunTwoArguments
    :: ( ExMemoryUsage a1
       , ExMemoryUsage a2
       )
    => CostingFun ModelTwoArguments
    -> a1
    -> a2
    -> ExBudgetStream
runCostingFunTwoArguments (CostingFun cpu mem) =
    case (runTwoArgumentModel cpu, runTwoArgumentModel mem) of
        (!runCpu, !runMem) -> onMemoryUsages $ \mem1 mem2 ->
            zipCostStream
                (runCpu mem1 mem2)
                (runMem mem1 mem2)
{-# INLINE runCostingFunTwoArguments #-}

-- | Take an intercept, two slopes and two streams, and scale each element of
-- the first stream by the first slope, each element of the second stream by the
-- second slope, add the two scaled streams together, and cons the intercept to
-- the stream afterwards.
scaleLinearlyTwoVariables :: Intercept -> Slope -> CostStream -> Slope -> CostStream -> CostStream
scaleLinearlyTwoVariables (Intercept intercept) (Slope slope1) stream1 (Slope slope2) stream2 =
    addCostStream
    (CostLast intercept)
    (addCostStream
     (mapCostStream (slope1 *) stream1)
     (mapCostStream (slope2 *) stream2)
    )
{-# INLINE scaleLinearlyTwoVariables #-}

runTwoArgumentModel
    :: ModelTwoArguments
    -> CostStream
    -> CostStream
    -> CostStream
runTwoArgumentModel
    (ModelTwoArgumentsConstantCost c) = lazy $ \_ _ -> CostLast c
runTwoArgumentModel
    (ModelTwoArgumentsAddedSizes (OneVariableLinearFunction intercept slope)) =
        lazy $ \costs1 costs2 ->
            scaleLinearly intercept slope $ addCostStream costs1 costs2
runTwoArgumentModel
    (ModelTwoArgumentsSubtractedSizes (ModelSubtractedSizes intercept slope minSize)) =
        lazy $ \costs1 costs2 -> do
            let !size1 = sumCostStream costs1
                !size2 = sumCostStream costs2
            scaleLinearly intercept slope $ CostLast (max minSize $ size1 - size2)
runTwoArgumentModel
    (ModelTwoArgumentsMultipliedSizes (OneVariableLinearFunction intercept slope)) =
        lazy $ \costs1 costs2 -> do
            let !size1 = sumCostStream costs1
                !size2 = sumCostStream costs2
            scaleLinearly intercept slope $ CostLast (size1 * size2)
runTwoArgumentModel
    (ModelTwoArgumentsMinSize (OneVariableLinearFunction intercept slope)) =
        lazy $ \costs1 costs2 -> do
            scaleLinearly intercept slope $ minCostStream costs1 costs2
runTwoArgumentModel
    (ModelTwoArgumentsMaxSize (OneVariableLinearFunction intercept slope)) =
        lazy $ \costs1 costs2 -> do
            let !size1 = sumCostStream costs1
                !size2 = sumCostStream costs2
            scaleLinearly intercept slope $ CostLast (max size1 size2)
runTwoArgumentModel
    (ModelTwoArgumentsLinearInX (OneVariableLinearFunction intercept slope)) =
        lazy $ \costs1 _ ->
            scaleLinearly intercept slope costs1
runTwoArgumentModel
    (ModelTwoArgumentsLinearInY (OneVariableLinearFunction intercept slope)) =
        lazy $ \_ costs2 ->
            scaleLinearly intercept slope costs2
runTwoArgumentModel
    (ModelTwoArgumentsLinearInXAndY (TwoVariableLinearFunction intercept slope1 slope2)) =
        lazy $ \costs1 costs2 ->
            scaleLinearlyTwoVariables intercept slope1 costs1 slope2 costs2
runTwoArgumentModel
    -- Off the diagonal, return the constant.  On the diagonal, run the other model.
    (ModelTwoArgumentsConstOffDiagonal (ModelConstantOrOneArgument c m)) =
        case runOneArgumentModel m of
            !run -> lazy $ \costs1 costs2 -> do
                let !size1 = sumCostStream costs1
                    !size2 = sumCostStream costs2
                if size1 /= size2
                    then CostLast c
                    else run (CostLast size1)
runTwoArgumentModel
    -- Below the diagonal, return the constant. Above the diagonal, run the other model.
    (ModelTwoArgumentsConstBelowDiagonal (ModelConstantOrTwoArguments c m)) =
        case runTwoArgumentModel m of
            !run -> lazy $ \costs1 costs2 -> do
                let !size1 = sumCostStream costs1
                    !size2 = sumCostStream costs2
                if size1 > size2
                    then CostLast c
                    else run (CostLast size1) (CostLast size2)
runTwoArgumentModel
    -- Above the diagonal, return the constant. Below the diagonal, run the other model.
    (ModelTwoArgumentsConstAboveDiagonal (ModelConstantOrTwoArguments c m)) =
        case runTwoArgumentModel m of
            !run -> lazy $ \costs1 costs2 -> do
                let !size1 = sumCostStream costs1
                    !size2 = sumCostStream costs2
                if size1 < size2
                    then CostLast c
                    else run (CostLast size1) (CostLast size2)
runTwoArgumentModel
    (ModelTwoArgumentsQuadraticInY f) =
        lazy $ \_ costs2 ->
            CostLast $ evaluateOneVariableQuadraticFunction f $ sumCostStream costs2
{-# NOINLINE runTwoArgumentModel #-}


---------------- Three-argument costing functions ----------------

data ModelThreeArguments =
    ModelThreeArgumentsConstantCost          CostingInteger
  | ModelThreeArgumentsAddedSizes            OneVariableLinearFunction
  | ModelThreeArgumentsLinearInX             OneVariableLinearFunction
  | ModelThreeArgumentsLinearInY             OneVariableLinearFunction
  | ModelThreeArgumentsLinearInZ             OneVariableLinearFunction
  | ModelThreeArgumentsQuadraticInZ          OneVariableQuadraticFunction
  | ModelThreeArgumentsLiteralInYOrLinearInZ OneVariableLinearFunction
    deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

instance Default ModelThreeArguments where
    def = ModelThreeArgumentsConstantCost maxBound

instance UnimplementedCostingFun ModelThreeArguments where
  unimplementedCostingFun = makeUnimplementedCostingFun ModelThreeArgumentsConstantCost

runThreeArgumentModel
    :: ModelThreeArguments
    -> CostStream
    -> CostStream
    -> CostStream
    -> CostStream
runThreeArgumentModel (ModelThreeArgumentsConstantCost c) = lazy $ \_ _ _ -> CostLast c
runThreeArgumentModel
    (ModelThreeArgumentsAddedSizes (OneVariableLinearFunction intercept slope)) =
        lazy $ \costs1 costs2 costs3 ->
            scaleLinearly intercept slope . addCostStream costs1 $ addCostStream costs2 costs3
runThreeArgumentModel
    (ModelThreeArgumentsLinearInX (OneVariableLinearFunction intercept slope)) =
        lazy $ \costs1 _ _ ->
            scaleLinearly intercept slope costs1
runThreeArgumentModel
    (ModelThreeArgumentsLinearInY (OneVariableLinearFunction intercept slope)) =
        lazy $ \_ costs2 _ ->
            scaleLinearly intercept slope costs2
runThreeArgumentModel
    (ModelThreeArgumentsLinearInZ (OneVariableLinearFunction intercept slope)) =
        lazy $ \_ _ costs3 ->
            scaleLinearly intercept slope costs3
runThreeArgumentModel
    (ModelThreeArgumentsQuadraticInZ f) =
        lazy $ \_ _ costs3 -> CostLast $ evaluateOneVariableQuadraticFunction f $ sumCostStream costs3
{- Either a literal number of bytes or a linear function.  This is for
   `integerToByteString`, where if the second argument is zero, the output
   bytestring has the minimum length required to contain the converted integer,
   but if the second argument is nonzero it specifies the exact length of the
   output bytestring. -}
runThreeArgumentModel
    (ModelThreeArgumentsLiteralInYOrLinearInZ (OneVariableLinearFunction intercept slope)) =
        lazy $ \_ costs2 costs3 ->
            let width = sumCostStream costs2
            in if width == 0
            then scaleLinearly intercept slope costs3
            else costs2
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
    -> ExBudgetStream
runCostingFunThreeArguments (CostingFun cpu mem) =
    case (runThreeArgumentModel cpu, runThreeArgumentModel mem) of
        (!runCpu, !runMem) -> onMemoryUsages $ \mem1 mem2 mem3 ->
            zipCostStream
                (runCpu mem1 mem2 mem3)
                (runMem mem1 mem2 mem3)
{-# INLINE runCostingFunThreeArguments #-}


---------------- Four-argument costing functions ----------------

data ModelFourArguments =
      ModelFourArgumentsConstantCost CostingInteger
    deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

instance Default ModelFourArguments where
    def = ModelFourArgumentsConstantCost maxBound

instance UnimplementedCostingFun ModelFourArguments where
  unimplementedCostingFun = makeUnimplementedCostingFun ModelFourArgumentsConstantCost

runFourArgumentModel
    :: ModelFourArguments
    -> CostStream
    -> CostStream
    -> CostStream
    -> CostStream
    -> CostStream
runFourArgumentModel (ModelFourArgumentsConstantCost c) = lazy $ \_ _ _ _ -> CostLast c
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
    -> ExBudgetStream
runCostingFunFourArguments (CostingFun cpu mem) =
    case (runFourArgumentModel cpu, runFourArgumentModel mem) of
        (!runCpu, !runMem) -> onMemoryUsages $ \mem1 mem2 mem3 mem4 ->
            zipCostStream
                (runCpu mem1 mem2 mem3 mem4)
                (runMem mem1 mem2 mem3 mem4)
{-# INLINE runCostingFunFourArguments #-}


---------------- Five-argument costing functions ----------------

data ModelFiveArguments =
      ModelFiveArgumentsConstantCost CostingInteger
    deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

instance Default ModelFiveArguments where
    def = ModelFiveArgumentsConstantCost maxBound

instance UnimplementedCostingFun ModelFiveArguments where
  unimplementedCostingFun = makeUnimplementedCostingFun ModelFiveArgumentsConstantCost

runFiveArgumentModel
    :: ModelFiveArguments
    -> CostStream
    -> CostStream
    -> CostStream
    -> CostStream
    -> CostStream
    -> CostStream
runFiveArgumentModel (ModelFiveArgumentsConstantCost c) = lazy $ \_ _ _ _ _ -> CostLast c
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
    -> ExBudgetStream
runCostingFunFiveArguments (CostingFun cpu mem) =
    case (runFiveArgumentModel cpu, runFiveArgumentModel mem) of
        (!runCpu, !runMem) -> onMemoryUsages $ \mem1 mem2 mem3 mem4 mem5 ->
            zipCostStream
                (runCpu mem1 mem2 mem3 mem4 mem5)
                (runMem mem1 mem2 mem3 mem4 mem5)
{-# INLINE runCostingFunFiveArguments #-}

---------------- Six-argument costing functions ----------------

data ModelSixArguments =
      ModelSixArgumentsConstantCost CostingInteger
    deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

instance Default ModelSixArguments where
    def = ModelSixArgumentsConstantCost maxBound

instance UnimplementedCostingFun ModelSixArguments where
  unimplementedCostingFun = makeUnimplementedCostingFun ModelSixArgumentsConstantCost

runSixArgumentModel
    :: ModelSixArguments
    -> CostStream
    -> CostStream
    -> CostStream
    -> CostStream
    -> CostStream
    -> CostStream
    -> CostStream
runSixArgumentModel (ModelSixArgumentsConstantCost c) = lazy $ \_ _ _ _ _ _ -> CostLast c
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
    -> ExBudgetStream
runCostingFunSixArguments (CostingFun cpu mem) =
    case (runSixArgumentModel cpu, runSixArgumentModel mem) of
        (!runCpu, !runMem) -> onMemoryUsages $ \mem1 mem2 mem3 mem4 mem5 mem6 ->
            zipCostStream
                (runCpu mem1 mem2 mem3 mem4 mem5 mem6)
                (runMem mem1 mem2 mem3 mem4 mem5 mem6)
{-# INLINE runCostingFunSixArguments #-}
