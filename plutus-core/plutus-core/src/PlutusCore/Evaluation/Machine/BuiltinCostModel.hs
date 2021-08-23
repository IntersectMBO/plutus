{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE StrictData           #-}

module PlutusCore.Evaluation.Machine.BuiltinCostModel
    ( BuiltinCostModel
    , BuiltinCostModelBase(..)
    , CostingFun(..)
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

import           PlutusPrelude                          hiding (toList)

import           PlutusCore.Evaluation.Machine.ExBudget
import           PlutusCore.Evaluation.Machine.ExMemory

import           Barbies
import           Data.Aeson
import           Data.Default.Class
import           Data.Hashable
import qualified Data.Kind                              as Kind
import           Deriving.Aeson
import           Language.Haskell.TH.Syntax             hiding (Name, newName)

type BuiltinCostModel = BuiltinCostModelBase CostingFun

-- See  Note [Budgeting units] in ExBudgeting.hs

-- If the types here change there may be difficulties compiling this file
-- because it doesn't match builtinCostModel.json (which is parsed during
-- compilation).  In that case, manually change the JSON to match or do what it
-- says in Note [Modifying the cost model] in ExBudgetingDefaults.hs.

-- | The main model which contains all data required to predict the cost of
-- builtin functions. See Note [Creation of the Cost Model] for how this is
-- generated. Calibrated for the CEK machine.

-- See Note [Modifying the cost model] in ExBudgetingDefaults.hs for an
-- explanation of how to regenerate the cost model file when this is changed.


{- | Many of the builtins have simple costs in for certain combinations of
   arguments but more complicated costs for other combinations: for example,
   equalsByteString will return imemdiately if the arguments have different
   lengths, and divideInteger a b will return immediately if a<b.  This type
   allows us to say exactly where the cost model applies (for a small selection
   of common situations) and only run the full costing function if necessary,
   returning a small cost (currently zero) otherwise. This is also helpful
   because we can't fit a sensible model to something like divideInteger, where
   costs really are zero above the diagonal but very complicated below it).
-}
data Support
    = Everywhere
    | OnDiagonal
    | BelowOrOnDiagonal
    | AboveOrOnDiagonal
    deriving (Show, Eq, Generic, Lift, NFData)

data BuiltinCostModelBase f =
    BuiltinCostModelBase
    {
      -- Integers
      paramAddInteger               :: f ModelTwoArguments
    , paramSubtractInteger          :: f ModelTwoArguments
    , paramMultiplyInteger          :: f ModelTwoArguments
    , paramDivideInteger            :: f ModelTwoArguments
    , paramQuotientInteger          :: f ModelTwoArguments
    , paramRemainderInteger         :: f ModelTwoArguments
    , paramModInteger               :: f ModelTwoArguments
    , paramEqualsInteger            :: f ModelTwoArguments
    , paramLessThanInteger          :: f ModelTwoArguments
    , paramLessThanEqualsInteger    :: f ModelTwoArguments
    -- Bytestrings
    , paramAppendByteString         :: f ModelTwoArguments
    , paramConsByteString           :: f ModelTwoArguments
    , paramSliceByteString          :: f ModelThreeArguments
    , paramLengthOfByteString       :: f ModelOneArgument
    , paramIndexByteString          :: f ModelTwoArguments
    , paramEqualsByteString         :: f ModelTwoArguments
    , paramLessThanByteString       :: f ModelTwoArguments
    , paramLessThanEqualsByteString :: f ModelTwoArguments
    -- Cryptography and hashes
    , paramSha2_256                 :: f ModelOneArgument
    , paramSha3_256                 :: f ModelOneArgument
    , paramBlake2b                  :: f ModelOneArgument
       -- ^ This should really be paramBlake2b_256, but changing it might be
       -- problematic because then the names of the cost model parameters used
       -- by the ledger would change as well.
    , paramVerifySignature          :: f ModelThreeArguments
    -- Strings
    , paramAppendString             :: f ModelTwoArguments
    , paramEqualsString             :: f ModelTwoArguments
    , paramEncodeUtf8               :: f ModelOneArgument
    , paramDecodeUtf8               :: f ModelOneArgument
    -- Bool
    , paramIfThenElse               :: f ModelThreeArguments
    -- Unit
    , paramChooseUnit               :: f ModelTwoArguments
    -- Tracing
    , paramTrace                    :: f ModelTwoArguments
    -- Pairs
    , paramFstPair                  :: f ModelOneArgument
    , paramSndPair                  :: f ModelOneArgument
    -- Lists
    , paramChooseList               :: f ModelThreeArguments
    , paramMkCons                   :: f ModelTwoArguments
    , paramHeadList                 :: f ModelOneArgument
    , paramTailList                 :: f ModelOneArgument
    , paramNullList                 :: f ModelOneArgument
    -- Data
    , paramChooseData               :: f ModelSixArguments
    , paramConstrData               :: f ModelTwoArguments
    , paramMapData                  :: f ModelOneArgument
    , paramListData                 :: f ModelOneArgument
    , paramIData                    :: f ModelOneArgument
    , paramBData                    :: f ModelOneArgument
    , paramUnConstrData             :: f ModelOneArgument
    , paramUnMapData                :: f ModelOneArgument
    , paramUnListData               :: f ModelOneArgument
    , paramUnIData                  :: f ModelOneArgument
    , paramUnBData                  :: f ModelOneArgument
    , paramEqualsData               :: f ModelTwoArguments
    -- Misc constructors
    , paramMkPairData               :: f ModelTwoArguments
    , paramMkNilData                :: f ModelOneArgument
    , paramMkNilPairData            :: f ModelOneArgument
    }
    deriving (Generic, FunctorB, TraversableB, ConstraintsB)

deriving via CustomJSON '[FieldLabelModifier (StripPrefix "param", LowerIntialCharacter)]
             (BuiltinCostModelBase CostingFun) instance ToJSON (BuiltinCostModelBase CostingFun)
deriving via CustomJSON '[FieldLabelModifier (StripPrefix "param", LowerIntialCharacter)]
             (BuiltinCostModelBase CostingFun) instance FromJSON (BuiltinCostModelBase CostingFun)


-- Needed to help derive various instances for BuiltinCostModelBase
type AllArgumentModels (constraint :: Kind.Type -> Kind.Constraint) f =
    ( constraint (f ModelOneArgument)
    , constraint (f ModelTwoArguments)
    , constraint (f ModelThreeArguments)
    , constraint (f ModelFourArguments)
    , constraint (f ModelFiveArguments)
    , constraint (f ModelSixArguments))

-- HLS doesn't like the AllBF from Barbies.
deriving instance AllArgumentModels NFData  f => NFData  (BuiltinCostModelBase f)
deriving instance AllArgumentModels Default f => Default (BuiltinCostModelBase f)
deriving instance AllArgumentModels Lift    f => Lift    (BuiltinCostModelBase f)
deriving instance AllArgumentModels Show    f => Show    (BuiltinCostModelBase f)
deriving instance AllArgumentModels Eq      f => Eq      (BuiltinCostModelBase f)

-- TODO there's probably a nice way to abstract over the number of arguments here. Feel free to implement it.

data CostingFun model = CostingFun
    { costingFunCpu    :: model
    , costingFunMemory :: model
    }
    deriving (Show, Eq, Generic, Lift, Default, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "costingFun", CamelToSnake)] (CostingFun model)


---------------- One-argument costing functions ----------------

data ModelOneArgument =
    ModelOneArgumentConstantCost CostingInteger
    | ModelOneArgumentLinearCost ModelLinearSize
    deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[ TagSingleConstructors
         , SumTaggedObject "type" "arguments"
         , ConstructorTagModifier (StripPrefix "ModelOneArgument", CamelToSnake)]
        ModelOneArgument
        -- Without TagSingleConstructors the format can change unexpectedly if
        -- you add/remove constructors because you don't get the tags if there's
        -- only one constructor but you do if there's more than one.
instance Default ModelOneArgument where
    def = ModelOneArgumentConstantCost 0

runCostingFunOneArgument
    :: CostingFun ModelOneArgument
    -> ExMemory
    -> ExBudget
runCostingFunOneArgument
    (CostingFun cpu mem) mem1 =
        ExBudget (ExCPU    $ runOneArgumentModel cpu mem1)
                 (ExMemory $ runOneArgumentModel mem mem1)

runOneArgumentModel
    :: ModelOneArgument
    -> ExMemory
    -> CostingInteger
runOneArgumentModel (ModelOneArgumentConstantCost c) _ = c
runOneArgumentModel (ModelOneArgumentLinearCost (ModelLinearSize intercept slope)) (ExMemory s) =
    s * slope + intercept


---------------- Two-argument costing functions ----------------

-- | s * (x + y) + I
data ModelAddedSizes = ModelAddedSizes
    { modelAddedSizesIntercept :: CostingInteger
    , modelAddedSizesSlope     :: CostingInteger
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelAddedSizes", CamelToSnake)] ModelAddedSizes

-- | s * (x - y) + I
data ModelSubtractedSizes = ModelSubtractedSizes
    { modelSubtractedSizesIntercept :: CostingInteger
    , modelSubtractedSizesSlope     :: CostingInteger
    , modelSubtractedSizesMinimum   :: CostingInteger
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelSubtractedSizes", CamelToSnake)] ModelSubtractedSizes

data ModelLinearSize = ModelLinearSize
    { modelLinearSizeIntercept :: CostingInteger
    , modelLinearSizeSlope     :: CostingInteger
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelLinearSize", CamelToSnake)] ModelLinearSize

-- | s * (x * y) + I
data ModelMultipliedSizes = ModelMultipliedSizes
    { modelMultipliedSizesIntercept :: CostingInteger
    , modelMultipliedSizesSlope     :: CostingInteger
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelMultipliedSizes", CamelToSnake)] ModelMultipliedSizes

-- | s * min(x, y) + I
data ModelMinSize = ModelMinSize
    { modelMinSizeIntercept :: CostingInteger
    , modelMinSizeSlope     :: CostingInteger
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelMinSize", CamelToSnake)] ModelMinSize

-- | s * max(x, y) + I
data ModelMaxSize = ModelMaxSize
    { modelMaxSizeIntercept :: CostingInteger
    , modelMaxSizeSlope     :: CostingInteger
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelMaxSize", CamelToSnake)] ModelMaxSize

-- | if p then s*x else c; p depends on usage
data ModelConstantOrLinear = ModelConstantOrLinear
    { modelConstantOrLinearConstant  :: CostingInteger
    , modelConstantOrLinearIntercept :: CostingInteger
    , modelConstantOrLinearSlope     :: CostingInteger
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelConstantOrLinear", CamelToSnake)] ModelConstantOrLinear

-- | if p then s*x else c; p depends on usage
data ModelConstantOrTwoArguments = ModelConstantOrTwoArguments
    { modelConstantOrTwoArgumentsConstant :: CostingInteger
    , modelConstantOrTwoArgumentsModel    :: ModelTwoArguments
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelConstantOrTwoArguments", CamelToSnake)] ModelConstantOrTwoArguments


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
    deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[ TagSingleConstructors
         , SumTaggedObject "type" "arguments"
         , ConstructorTagModifier (StripPrefix "ModelTwoArguments", CamelToSnake)]
        ModelTwoArguments

instance Default ModelTwoArguments where
    def = ModelTwoArgumentsConstantCost 0

runCostingFunTwoArguments
    :: CostingFun ModelTwoArguments
    -> ExMemory
    -> ExMemory
    -> ExBudget
runCostingFunTwoArguments (CostingFun cpu mem) mem1 mem2 =
    ExBudget (ExCPU    $ runTwoArgumentModel cpu mem1 mem2)
             (ExMemory $ runTwoArgumentModel mem mem1 mem2)

runTwoArgumentModel
    :: ModelTwoArguments
    -> ExMemory
    -> ExMemory
    -> CostingInteger
runTwoArgumentModel
    (ModelTwoArgumentsConstantCost c) _ _ = c
runTwoArgumentModel
    (ModelTwoArgumentsAddedSizes (ModelAddedSizes intercept slope)) (ExMemory size1) (ExMemory size2) =
        (size1 + size2) * slope + intercept -- TODO is this even correct? If not, adjust the other implementations too.
runTwoArgumentModel
    (ModelTwoArgumentsSubtractedSizes (ModelSubtractedSizes intercept slope minSize)) (ExMemory size1) (ExMemory size2) =
        (max minSize (size1 - size2)) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsMultipliedSizes (ModelMultipliedSizes intercept slope)) (ExMemory size1) (ExMemory size2) =
        (size1 * size2) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsMinSize (ModelMinSize intercept slope)) (ExMemory size1) (ExMemory size2) =
        (min size1 size2) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsMaxSize (ModelMaxSize intercept slope)) (ExMemory size1) (ExMemory size2) =
        (max size1 size2) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsLinearInX (ModelLinearSize intercept slope)) (ExMemory size1) (ExMemory _) =
        size1 * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsLinearInY (ModelLinearSize intercept slope)) (ExMemory _) (ExMemory size2) =
        size2 * slope + intercept
runTwoArgumentModel  -- Off the diagonal, return the constant.  On the diagonal, run the one-variable linear model.
    (ModelTwoArgumentsLinearOnDiagonal (ModelConstantOrLinear c intercept slope)) (ExMemory xSize) (ExMemory ySize) =
        if xSize == ySize
        then xSize * slope + intercept
        else c
runTwoArgumentModel -- Below the diagonal, return the constant. Above the diagonal, run the other model.
    (ModelTwoArgumentsConstBelowDiagonal (ModelConstantOrTwoArguments c m)) xMem yMem =
        if xMem > yMem
        then c
        else runTwoArgumentModel m xMem yMem
runTwoArgumentModel -- Above the diagonal, return the constant. Below the diagonal, run the other model.
    (ModelTwoArgumentsConstAboveDiagonal (ModelConstantOrTwoArguments c m)) xMem yMem =
        if xMem < yMem
        then c
        else runTwoArgumentModel m xMem yMem


---------------- Three-argument costing functions ----------------

data ModelThreeArguments =
    ModelThreeArgumentsConstantCost CostingInteger
  | ModelThreeArgumentsAddedSizes   ModelAddedSizes
  | ModelThreeArgumentsLinearInZ    ModelLinearSize
    deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[ TagSingleConstructors
         , SumTaggedObject "type" "arguments"
         , ConstructorTagModifier (StripPrefix "ModelThreeArguments", CamelToSnake)]
        ModelThreeArguments

instance Default ModelThreeArguments where
    def = ModelThreeArgumentsConstantCost 0

runThreeArgumentModel
    :: ModelThreeArguments
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> CostingInteger
runThreeArgumentModel (ModelThreeArgumentsConstantCost c) _ _ _ = c
runThreeArgumentModel (ModelThreeArgumentsAddedSizes (ModelAddedSizes intercept slope)) (ExMemory size1) (ExMemory size2) (ExMemory size3) =
    (size1 + size2 + size3) * slope + intercept
runThreeArgumentModel (ModelThreeArgumentsLinearInZ (ModelLinearSize intercept slope)) _ _ (ExMemory size3) =
    size3 * slope + intercept

runCostingFunThreeArguments
    :: CostingFun ModelThreeArguments
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExBudget
runCostingFunThreeArguments (CostingFun cpu mem) mem1 mem2 mem3 =
    ExBudget (ExCPU    $ runThreeArgumentModel cpu mem1 mem2 mem3)
             (ExMemory $ runThreeArgumentModel mem mem1 mem2 mem3)


---------------- Four-argument costing functions ----------------

data ModelFourArguments =
      ModelFourArgumentsConstantCost CostingInteger
    deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[ TagSingleConstructors
         , SumTaggedObject "type" "arguments"
         , ConstructorTagModifier (StripPrefix "ModelFourArguments", CamelToSnake)]
        ModelFourArguments

instance Default ModelFourArguments where
    def = ModelFourArgumentsConstantCost 0

runFourArgumentModel
    :: ModelFourArguments
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> CostingInteger
runFourArgumentModel (ModelFourArgumentsConstantCost c) _ _ _ _ = c

runCostingFunFourArguments
    :: CostingFun ModelFourArguments
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExBudget
runCostingFunFourArguments (CostingFun cpu mem) mem1 mem2 mem3 mem4 =
    ExBudget (ExCPU    $ runFourArgumentModel cpu mem1 mem2 mem3 mem4)
             (ExMemory $ runFourArgumentModel mem mem1 mem2 mem3 mem4)


---------------- Five-argument costing functions ----------------

data ModelFiveArguments =
      ModelFiveArgumentsConstantCost CostingInteger
    deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[ TagSingleConstructors
         , SumTaggedObject "type" "arguments"
         , ConstructorTagModifier (StripPrefix "ModelFiveArguments", CamelToSnake)]
        ModelFiveArguments

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
runFiveArgumentModel (ModelFiveArgumentsConstantCost c) _ _ _ _ _ = c

runCostingFunFiveArguments
    :: CostingFun ModelFiveArguments
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExBudget
runCostingFunFiveArguments (CostingFun cpu mem) mem1 mem2 mem3 mem4 mem5 =
    ExBudget (ExCPU    $ runFiveArgumentModel cpu mem1 mem2 mem3 mem4 mem5)
             (ExMemory $ runFiveArgumentModel mem mem1 mem2 mem3 mem4 mem5)


---------------- Six-argument costing functions ----------------

data ModelSixArguments =
      ModelSixArgumentsConstantCost CostingInteger
    deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[ TagSingleConstructors
         , SumTaggedObject "type" "arguments"
         , ConstructorTagModifier (StripPrefix "ModelSixArguments", CamelToSnake)]
        ModelSixArguments

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
runSixArgumentModel (ModelSixArgumentsConstantCost c) _ _ _ _ _ _ = c

runCostingFunSixArguments
    :: CostingFun ModelSixArguments
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExMemory
    -> ExBudget
runCostingFunSixArguments (CostingFun cpu mem) mem1 mem2 mem3 mem4 mem5 mem6 =
    ExBudget (ExCPU    $ runSixArgumentModel cpu mem1 mem2 mem3 mem4 mem5 mem6)
             (ExMemory $ runSixArgumentModel mem mem1 mem2 mem3 mem4 mem5 mem6)

