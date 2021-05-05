{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE StrictData           #-}

module PlutusCore.Evaluation.Machine.ExBudgeting
    ( CostModel
    , CostModelBase(..)
    , CostingFun(..)
    , ModelAddedSizes(..)
    , ModelSubtractedSizes(..)
    , ModelOrientation(..)
    , ModelLinearSize(..)
    , ModelMultipliedSizes(..)
    , ModelMinSize(..)
    , ModelMaxSize(..)
    , ModelSplitConst(..)
    , ModelOneArgument(..)
    , ModelTwoArguments(..)
    , ModelThreeArguments(..)
    , runCostingFunOneArgument
    , runCostingFunTwoArguments
    , runCostingFunThreeArguments
    , toCostUnit
    , fromCostUnit
    , Hashable
    , CostModelParams
    , extractModelParams
    , applyModelParams
    )
where

import           PlutusPrelude                          hiding (toList)

import           PlutusCore.Evaluation.Machine.ExBudget
import           PlutusCore.Evaluation.Machine.ExMemory

import           Barbies
import           Data.Aeson
import           Data.Aeson.Flatten
import           Data.Default.Class
import qualified Data.HashMap.Strict                    as HM
import           Data.Hashable
import qualified Data.Kind                              as Kind
import qualified Data.Map                               as Map
import qualified Data.Scientific                        as S
import qualified Data.Text                              as Text
import           Deriving.Aeson
import           Language.Haskell.TH.Syntax             hiding (Name, newName)

type CostModel = CostModelBase CostingFun


{- | Convert a cost prediction to an integer.  The coefficients in the cost models
   are often very small, so if you convert cost model predictions directly to
   integers the results are very coarsely distributed.  Here we scale the
   results up to make them more granular, which makes their contributions to the
   overall cost model much more significant (variations in execution times are
   much more likely to be reflected by predictions).  Exactly what we do here
   may change as the final form of the cost model becomes more firmly decided.
   Note also that it's important to perform the same adjustments on the R output
   in TestCostModel.hs so that Haskell and R results agree (which is why
   `toCostUnit` is exported).
-}

{- Note [Time units]. What are the units?  The Criterion output produces times in
   seconds, and these are usually very small, typically of the order of 10^-6.
   In models.R, the get.bench.data funtion multiplies everything by 10^6 after
   reading it in, so it (and the models it outputs) deal with times in
   microseconds.  So for example the model for "addInteger" may have an
   intercept of 0.249487779229322 and a slope of 1.87065741871939e-3.  This
   means that it's taking a basic time of 249ns plus another 1.87ns for every
   word in the input (in fact, for the maximum of the number of words in the
   input).  This is still very small, so here we're scaling up by another 10^6,
   to get times in picoseconds.  For the addInteger example we'll now have an
   intercept of 249000ps plus another 1870 for each word in the input. -}

costMultiplier :: Integer
costMultiplier = 1000 * 1000

toCostUnit :: Double -> Integer
toCostUnit x = ceiling ((fromInteger costMultiplier) * x)

fromCostUnit :: Integer -> Integer
fromCostUnit x = x `div` costMultiplier

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

{- Note [Cost model parameters]
We want to expose to the ledger some notion of the "cost model parameters". Intuitively, these should be all the numbers that appear in the cost model.

However, there are quite a few quirks to deal with.

1. CostModel is stuctured

That is, it's a complex data structure and the numbers in question are often nested inside it.
To deal with this quickly, we take the ugly approach of operating on the JSON representation of the model.
We flatten this down into a simple key-value mapping (see 'flattenObject' and 'unflattenObject'), and then
look only at the numbers.

2. We use floats, not integers

We'd really prefer to expose integers as our parameters - they're just better behaved, and really we'd like to use integers
internally too for determinism reasons. So we pretend that we have integers by scaling up all our numbers by 1000 and taking
the integral floor, at some loss of precision.

Once we use integers internally this will be simpler.

3. CostModel includes the *type* of the model, which isn't a parameter

We can just strip the out, but in particular this means that the parameters are not enough to *construct* a model.
So we punt and say that you can *update* a model by giving the parameters. So you can take the default model and then
overwrite the parameters, which seems okay.

This is also implemented in a horrible JSON-y way.

4. The implementation is not nice

Ugly JSON stuff and failure possibilities where there probably shouldn't be any.
-}

-- See Note [Cost model parameters]
type CostModelParams = Map.Map Text.Text Integer

-- See Note [Cost model parameters]
-- | Extract the model parameters from a model.
extractModelParams :: CostModel -> Maybe CostModelParams
extractModelParams cm = case toJSON cm of
    Object o ->
        let
            flattened = flattenObject "-" o
            toScaledInteger :: S.Scientific -> Integer
            toScaledInteger n = floor (n*1000)
            scaledNumbers = HM.mapMaybe (\case { Number n -> Just $ toScaledInteger n; _ -> Nothing }) flattened
            mapified = Map.fromList $ HM.toList scaledNumbers
        in Just mapified
    _ -> Nothing

-- See Note [Cost model parameters]
-- | Update a model by overwriting the parameters with the given ones.
applyModelParams :: CostModel -> CostModelParams -> Maybe CostModel
applyModelParams cm params = case toJSON cm of
    Object o ->
        let
            hashmapified = HM.fromList $ Map.toList params
            scaledNumbers = fmap (\n -> Number $ fromIntegral n / 1000) hashmapified
            flattened = flattenObject "-" o
            -- this is where the overwriting happens, this is left-biased
            merged = HM.union scaledNumbers flattened
            unflattened = unflattenObject "-" merged
        in case fromJSON (Object unflattened) of
            Success a -> Just a
            Error _   -> Nothing
    _ -> Nothing

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
    ModelOneArgumentConstantCost Double
    | ModelOneArgumentLinearCost ModelLinearSize
    deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[SumTaggedObject "type" "arguments", ConstructorTagModifier (StripPrefix "ModelOneArgument", CamelToSnake)] ModelOneArgument
instance Default ModelOneArgument where
    def = ModelOneArgumentConstantCost 0.0

runCostingFunOneArgument :: CostingFun ModelOneArgument -> ExMemory -> ExBudget
runCostingFunOneArgument
    (CostingFun cpu mem) mem1 =
        ExBudget (ExCPU (runOneArgumentModel cpu mem1)) (ExMemory (runOneArgumentModel mem mem1))

runOneArgumentModel :: ModelOneArgument -> ExMemory -> Integer
runOneArgumentModel (ModelOneArgumentConstantCost c) _ = toCostUnit c
runOneArgumentModel (ModelOneArgumentLinearCost (ModelLinearSize intercept slope _)) (ExMemory s) =
    toCostUnit $ (fromInteger s) * slope + intercept

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
data ModelMultipliedSizes = ModelMultipliedSizes
    { modelMultipliedSizesIntercept :: Double
    , modelMultipliedSizesSlope     :: Double
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelMultipliedSizes", CamelToSnake)] ModelMultipliedSizes

-- | s * min(x, y) + I
data ModelMinSize = ModelMinSize
    { modelMinSizeIntercept :: Double
    , modelMinSizeSlope     :: Double
    } deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[FieldLabelModifier (StripPrefix "modelMinSize", CamelToSnake)] ModelMinSize

-- | s * max(x, y) + I
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
      ModelTwoArgumentsConstantCost    Double
    | ModelTwoArgumentsAddedSizes      ModelAddedSizes
    | ModelTwoArgumentsSubtractedSizes ModelSubtractedSizes
    | ModelTwoArgumentsMultipliedSizes ModelMultipliedSizes
    | ModelTwoArgumentsMinSize         ModelMinSize
    | ModelTwoArgumentsMaxSize         ModelMaxSize
    | ModelTwoArgumentsSplitConstMulti ModelSplitConst
    | ModelTwoArgumentsLinearSize      ModelLinearSize
    deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[SumTaggedObject "type" "arguments", ConstructorTagModifier (StripPrefix "ModelTwoArguments", CamelToSnake)] ModelTwoArguments

instance Default ModelTwoArguments where
    def = ModelTwoArgumentsConstantCost 0.0

runCostingFunTwoArguments :: CostingFun ModelTwoArguments -> ExMemory -> ExMemory -> ExBudget
runCostingFunTwoArguments (CostingFun cpu mem) mem1 mem2 =
    ExBudget (ExCPU (runTwoArgumentModel cpu mem1 mem2)) (ExMemory (runTwoArgumentModel mem mem1 mem2))

runTwoArgumentModel :: ModelTwoArguments -> ExMemory -> ExMemory -> Integer
runTwoArgumentModel
    (ModelTwoArgumentsConstantCost c) _ _ = toCostUnit c
runTwoArgumentModel
    (ModelTwoArgumentsAddedSizes (ModelAddedSizes intercept slope)) (ExMemory size1) (ExMemory size2) =
        toCostUnit $ (fromInteger (size1 + size2)) * slope + intercept -- TODO is this even correct? If not, adjust the other implementations too.
runTwoArgumentModel
    (ModelTwoArgumentsSubtractedSizes (ModelSubtractedSizes intercept slope minSize)) (ExMemory size1) (ExMemory size2) =
        toCostUnit $ (max minSize (fromInteger (size1 - size2))) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsMultipliedSizes (ModelMultipliedSizes intercept slope)) (ExMemory size1) (ExMemory size2) =
        toCostUnit $ (fromInteger (size1 * size2)) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsMinSize (ModelMinSize intercept slope)) (ExMemory size1) (ExMemory size2) =
        toCostUnit $ (fromInteger (min size1 size2)) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsMaxSize (ModelMaxSize intercept slope)) (ExMemory size1) (ExMemory size2) =
        toCostUnit $ (fromInteger (max size1 size2)) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsSplitConstMulti (ModelSplitConst intercept slope)) (ExMemory size1) (ExMemory size2) =
        toCostUnit $ (if (size1 > size2) then (fromInteger size1) * (fromInteger size2) else 0) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsLinearSize (ModelLinearSize intercept slope ModelOrientationX)) (ExMemory size1) (ExMemory _) =
        toCostUnit $ (fromInteger size1) * slope + intercept
runTwoArgumentModel
    (ModelTwoArgumentsLinearSize (ModelLinearSize intercept slope ModelOrientationY)) (ExMemory _) (ExMemory size2) =
        toCostUnit $ (fromInteger size2) * slope + intercept

data ModelThreeArguments =
    ModelThreeArgumentsConstantCost Double
  | ModelThreeArgumentsAddedSizes ModelAddedSizes
    deriving (Show, Eq, Generic, Lift, NFData)
    deriving (FromJSON, ToJSON) via CustomJSON
        '[SumTaggedObject "type" "arguments", ConstructorTagModifier (StripPrefix "ModelThreeArguments", CamelToSnake)] ModelThreeArguments

instance Default ModelThreeArguments where
    def = ModelThreeArgumentsConstantCost 0.0

runThreeArgumentModel :: ModelThreeArguments -> ExMemory -> ExMemory -> ExMemory -> Integer
runThreeArgumentModel (ModelThreeArgumentsConstantCost c) _ _ _ = toCostUnit c
runThreeArgumentModel (ModelThreeArgumentsAddedSizes (ModelAddedSizes intercept slope)) (ExMemory size1) (ExMemory size2) (ExMemory size3) =
    toCostUnit $ (fromInteger (size1 + size2 + size3)) * slope + intercept

runCostingFunThreeArguments :: CostingFun ModelThreeArguments -> ExMemory -> ExMemory -> ExMemory -> ExBudget
runCostingFunThreeArguments (CostingFun cpu mem) mem1 mem2 mem3 =
    ExBudget (ExCPU $ runThreeArgumentModel cpu mem1 mem2 mem3) (ExMemory $ runThreeArgumentModel mem mem1 mem2 mem3)
