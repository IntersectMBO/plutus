-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

module CreateBuiltinCostModel (costModelsR, createBuiltinCostModel, microToPico)
where

import BuiltinMemoryModels (Id (..), builtinMemoryModels)

import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.ExMemory

import Barbies (bmap, bsequence)
import Control.Applicative (Const (Const, getConst))
import Data.Functor.Compose (Compose (Compose))
import Data.SatInt
import Data.Text (Text)
import Text.Printf (printf)

import H.Prelude (MonadR, R, Region)
import Language.R (SomeSEXP, fromSomeSEXP)
import Language.R.QQ (r)

{-| Convert microseconds represented as a float to picoseconds represented as a
CostingInteger.  We round up to be sure we don't underestimate anything. -}
microToPico :: Double -> CostingInteger
microToPico = unsafeToSatInt . ceiling . (1e6 *)

{- See CostModelGeneration.md for a description of what this does. -}

-- TODO some generics magic.
-- Mentioned in CostModel.md. Change here, change there.
-- The names of the models in R.
-- If you get one of these wrong you'll probably get a message saying
-- 'parse error (not enough input) at ""'.
builtinCostModelNames :: BuiltinCostModelBase (Const Text)
builtinCostModelNames =
  BuiltinCostModelBase
    { paramAddInteger = "addIntegerModel"
    , paramSubtractInteger = "subtractIntegerModel"
    , paramMultiplyInteger = "multiplyIntegerModel"
    , paramDivideInteger = "divideIntegerModel"
    , paramQuotientInteger = "quotientIntegerModel"
    , paramRemainderInteger = "remainderIntegerModel"
    , paramModInteger = "modIntegerModel"
    , paramEqualsInteger = "equalsIntegerModel"
    , paramLessThanInteger = "lessThanIntegerModel"
    , paramLessThanEqualsInteger = "lessThanEqualsIntegerModel"
    , paramAppendByteString = "appendByteStringModel"
    , paramConsByteString = "consByteStringModel"
    , paramSliceByteString = "sliceByteStringModel"
    , paramLengthOfByteString = "lengthOfByteStringModel"
    , paramIndexByteString = "indexByteStringModel"
    , paramEqualsByteString = "equalsByteStringModel"
    , paramLessThanByteString = "lessThanByteStringModel"
    , paramLessThanEqualsByteString = "lessThanEqualsByteStringModel"
    , paramSha2_256 = "sha2_256Model"
    , paramSha3_256 = "sha3_256Model"
    , paramBlake2b_256 = "blake2b_256Model"
    , paramVerifyEd25519Signature = "verifyEd25519SignatureModel"
    , paramVerifyEcdsaSecp256k1Signature = "verifyEcdsaSecp256k1SignatureModel"
    , paramVerifySchnorrSecp256k1Signature = "verifySchnorrSecp256k1SignatureModel"
    , paramAppendString = "appendStringModel"
    , paramEqualsString = "equalsStringModel"
    , paramEncodeUtf8 = "encodeUtf8Model"
    , paramDecodeUtf8 = "decodeUtf8Model"
    , paramIfThenElse = "ifThenElseModel"
    , paramChooseUnit = "chooseUnitModel"
    , paramTrace = "traceModel"
    , paramFstPair = "fstPairModel"
    , paramSndPair = "sndPairModel"
    , paramChooseList = "chooseListModel"
    , paramMkCons = "mkConsModel"
    , paramHeadList = "headListModel"
    , paramTailList = "tailListModel"
    , paramNullList = "nullListModel"
    , paramChooseData = "chooseDataModel"
    , paramConstrData = "constrDataModel"
    , paramMapData = "mapDataModel"
    , paramListData = "listDataModel"
    , paramIData = "iDataModel"
    , paramBData = "bDataModel"
    , paramUnConstrData = "unConstrDataModel"
    , paramUnMapData = "unMapDataModel"
    , paramUnListData = "unListDataModel"
    , paramUnIData = "unIDataModel"
    , paramUnBData = "unBDataModel"
    , paramEqualsData = "equalsDataModel"
    , paramMkPairData = "mkPairDataModel"
    , paramMkNilData = "mkNilDataModel"
    , paramMkNilPairData = "mkNilPairDataModel"
    , paramSerialiseData = "serialiseDataModel"
    , paramBls12_381_G1_add = "bls12_381_G1_addModel"
    , paramBls12_381_G1_neg = "bls12_381_G1_negModel"
    , paramBls12_381_G1_scalarMul = "bls12_381_G1_scalarMulModel"
    , paramBls12_381_G1_multiScalarMul = "bls12_381_G1_multiScalarMulModel"
    , paramBls12_381_G1_equal = "bls12_381_G1_equalModel"
    , paramBls12_381_G1_compress = "bls12_381_G1_compressModel"
    , paramBls12_381_G1_uncompress = "bls12_381_G1_uncompressModel"
    , paramBls12_381_G1_hashToGroup = "bls12_381_G1_hashToGroupModel"
    , paramBls12_381_G2_add = "bls12_381_G2_addModel"
    , paramBls12_381_G2_neg = "bls12_381_G2_negModel"
    , paramBls12_381_G2_scalarMul = "bls12_381_G2_scalarMulModel"
    , paramBls12_381_G2_multiScalarMul = "bls12_381_G2_multiScalarMulModel"
    , paramBls12_381_G2_equal = "bls12_381_G2_equalModel"
    , paramBls12_381_G2_compress = "bls12_381_G2_compressModel"
    , paramBls12_381_G2_uncompress = "bls12_381_G2_uncompressModel"
    , paramBls12_381_G2_hashToGroup = "bls12_381_G2_hashToGroupModel"
    , paramBls12_381_millerLoop = "bls12_381_millerLoopModel"
    , paramBls12_381_mulMlResult = "bls12_381_mulMlResultModel"
    , paramBls12_381_finalVerify = "bls12_381_finalVerifyModel"
    , paramBlake2b_224 = "blake2b_224Model"
    , paramKeccak_256 = "keccak_256Model"
    , paramIntegerToByteString = "integerToByteStringModel"
    , paramByteStringToInteger = "byteStringToIntegerModel"
    , paramAndByteString = "andByteStringModel"
    , paramOrByteString = "orByteStringModel"
    , paramXorByteString = "xorByteStringModel"
    , paramComplementByteString = "complementByteStringModel"
    , paramReadBit = "readBitModel"
    , paramWriteBits = "writeBitsModel"
    , paramReplicateByte = "replicateByteModel"
    , paramShiftByteString = "shiftByteStringModel"
    , paramRotateByteString = "rotateByteStringModel"
    , paramCountSetBits = "countSetBitsModel"
    , paramFindFirstSetBit = "findFirstSetBitModel"
    , paramRipemd_160 = "ripemd_160Model"
    , paramExpModInteger = "expModIntegerModel"
    , paramDropList = "dropListModel"
    , paramLengthOfArray = "lengthOfArrayModel"
    , paramListToArray = "listToArrayModel"
    , paramIndexArray = "indexArrayModel"
    , -- Builtin values
      paramLookupCoin = "lookupCoinModel"
    , paramValueContains = "valueContainsModel"
    , paramValueData = "valueDataModel"
    , paramUnValueData = "unValueDataModel"
    , paramInsertCoin = "insertCoinModel"
    , paramUnionValue = "unionValueModel"
    , paramScaleValue = "scaleValueModel"
    }

{-| Loads the models from R.
The "_hs" suffixes below make Haskell variables accessible inside [r| ... |] -}
costModelsR
  :: MonadR m
  => FilePath
  -> FilePath
  -> m (BuiltinCostModelBase (Const (SomeSEXP (Region m))))
costModelsR bmfile rfile = do
  list <-
    [r|
             source(rfile_hs)
             modelFun(bmfile_hs)
           |]
  let makeCostModelEntry name =
        let n = getConst name
         in Compose $ fmap Const $ [r| list_hs [[n_hs]] |]
  bsequence $ bmap makeCostModelEntry builtinCostModelNames

{-| Creates the cost model from a CSV benchmarking results file and a file
containing R modelling code.  Note that R must be initialised before this is
called, typically like this:
  withEmbeddedR defaultConfig $ runRegion $ createBuiltinCostModel ... -}
createBuiltinCostModel :: FilePath -> FilePath -> R s (BuiltinCostModelBase CostingFun)
createBuiltinCostModel bmfile rfile = do
  cpuModels :: BuiltinCostModelBase (Const (SomeSEXP s)) <- costModelsR bmfile rfile
  let getParams
        :: (SomeSEXP s -> R s model)
        -> (forall f. BuiltinCostModelBase f -> f model)
        -> R s (CostingFun model)
      getParams readCF param = do
        let memModel = getId $ param builtinMemoryModels
        cpuModel <- readCF $ getConst $ param cpuModels
        pure $ CostingFun cpuModel memModel

  -- Integers
  paramAddInteger <- getParams readCF2 paramAddInteger
  paramSubtractInteger <- getParams readCF2 paramSubtractInteger
  paramMultiplyInteger <- getParams readCF2 paramMultiplyInteger
  paramDivideInteger <- getParams readCF2 paramDivideInteger
  paramQuotientInteger <- getParams readCF2 paramQuotientInteger
  paramRemainderInteger <- getParams readCF2 paramRemainderInteger
  paramModInteger <- getParams readCF2 paramModInteger
  paramEqualsInteger <- getParams readCF2 paramEqualsInteger
  paramLessThanInteger <- getParams readCF2 paramLessThanInteger
  paramLessThanEqualsInteger <- getParams readCF2 paramLessThanEqualsInteger
  -- Bytestrings
  paramAppendByteString <- getParams readCF2 paramAppendByteString
  paramConsByteString <- getParams readCF2 paramConsByteString
  paramSliceByteString <- getParams readCF3 paramSliceByteString
  paramLengthOfByteString <- getParams readCF1 paramLengthOfByteString
  paramIndexByteString <- getParams readCF2 paramIndexByteString
  paramEqualsByteString <- getParams readCF2 paramEqualsByteString
  paramLessThanByteString <- getParams readCF2 paramLessThanByteString
  paramLessThanEqualsByteString <- getParams readCF2 paramLessThanEqualsByteString
  -- Cryptography and hashes
  paramSha2_256 <- getParams readCF1 paramSha2_256
  paramSha3_256 <- getParams readCF1 paramSha3_256
  paramBlake2b_256 <- getParams readCF1 paramBlake2b_256
  paramVerifyEd25519Signature <- getParams readCF3 paramVerifyEd25519Signature
  paramVerifyEcdsaSecp256k1Signature <- getParams readCF3 paramVerifyEcdsaSecp256k1Signature
  paramVerifySchnorrSecp256k1Signature <- getParams readCF3 paramVerifySchnorrSecp256k1Signature
  -- Strings
  paramAppendString <- getParams readCF2 paramAppendString
  paramEqualsString <- getParams readCF2 paramEqualsString
  paramEncodeUtf8 <- getParams readCF1 paramEncodeUtf8
  paramDecodeUtf8 <- getParams readCF1 paramDecodeUtf8
  -- Bool
  paramIfThenElse <- getParams readCF3 paramIfThenElse
  -- Unit
  paramChooseUnit <- getParams readCF2 paramChooseUnit
  -- Tracing
  paramTrace <- getParams readCF2 paramTrace
  -- Pairs
  paramFstPair <- getParams readCF1 paramFstPair
  paramSndPair <- getParams readCF1 paramSndPair
  -- Lists
  paramChooseList <- getParams readCF3 paramChooseList
  paramMkCons <- getParams readCF2 paramMkCons
  paramHeadList <- getParams readCF1 paramHeadList
  paramTailList <- getParams readCF1 paramTailList
  paramNullList <- getParams readCF1 paramNullList
  -- Data
  paramChooseData <- getParams readCF6 paramChooseData
  paramConstrData <- getParams readCF2 paramConstrData
  paramMapData <- getParams readCF1 paramMapData
  paramListData <- getParams readCF1 paramListData
  paramIData <- getParams readCF1 paramIData
  paramBData <- getParams readCF1 paramBData
  paramUnConstrData <- getParams readCF1 paramUnConstrData
  paramUnMapData <- getParams readCF1 paramUnMapData
  paramUnListData <- getParams readCF1 paramUnListData
  paramUnIData <- getParams readCF1 paramUnIData
  paramUnBData <- getParams readCF1 paramUnBData
  paramEqualsData <- getParams readCF2 paramEqualsData
  paramSerialiseData <- getParams readCF1 paramSerialiseData
  -- Misc constructors
  paramMkPairData <- getParams readCF2 paramMkPairData
  paramMkNilData <- getParams readCF1 paramMkNilData
  paramMkNilPairData <- getParams readCF1 paramMkNilPairData
  -- BLS12-381
  paramBls12_381_G1_add <- getParams readCF2 paramBls12_381_G1_add
  paramBls12_381_G1_neg <- getParams readCF1 paramBls12_381_G1_neg
  paramBls12_381_G1_scalarMul <- getParams readCF2 paramBls12_381_G1_scalarMul
  paramBls12_381_G1_multiScalarMul <- getParams readCF2 paramBls12_381_G1_multiScalarMul
  paramBls12_381_G1_equal <- getParams readCF2 paramBls12_381_G1_equal
  paramBls12_381_G1_compress <- getParams readCF1 paramBls12_381_G1_compress
  paramBls12_381_G1_uncompress <- getParams readCF1 paramBls12_381_G1_uncompress
  paramBls12_381_G1_hashToGroup <- getParams readCF2 paramBls12_381_G1_hashToGroup
  paramBls12_381_G2_add <- getParams readCF2 paramBls12_381_G2_add
  paramBls12_381_G2_neg <- getParams readCF1 paramBls12_381_G2_neg
  paramBls12_381_G2_scalarMul <- getParams readCF2 paramBls12_381_G2_scalarMul
  paramBls12_381_G2_multiScalarMul <- getParams readCF2 paramBls12_381_G2_multiScalarMul
  paramBls12_381_G2_equal <- getParams readCF2 paramBls12_381_G2_equal
  paramBls12_381_G2_compress <- getParams readCF1 paramBls12_381_G2_compress
  paramBls12_381_G2_uncompress <- getParams readCF1 paramBls12_381_G2_uncompress
  paramBls12_381_G2_hashToGroup <- getParams readCF2 paramBls12_381_G2_hashToGroup
  paramBls12_381_millerLoop <- getParams readCF2 paramBls12_381_millerLoop
  paramBls12_381_mulMlResult <- getParams readCF2 paramBls12_381_mulMlResult
  paramBls12_381_finalVerify <- getParams readCF2 paramBls12_381_finalVerify
  -- More hashes
  paramKeccak_256 <- getParams readCF1 paramKeccak_256
  paramBlake2b_224 <- getParams readCF1 paramBlake2b_224
  -- Bitwise operations
  paramByteStringToInteger <- getParams readCF2 paramByteStringToInteger
  paramIntegerToByteString <- getParams readCF3 paramIntegerToByteString
  paramAndByteString <- getParams readCF3 paramAndByteString
  paramOrByteString <- getParams readCF3 paramOrByteString
  paramXorByteString <- getParams readCF3 paramXorByteString
  paramComplementByteString <- getParams readCF1 paramComplementByteString
  paramReadBit <- getParams readCF2 paramReadBit
  paramWriteBits <- getParams readCF3 paramWriteBits
  paramReplicateByte <- getParams readCF2 paramReplicateByte
  paramShiftByteString <- getParams readCF2 paramShiftByteString
  paramRotateByteString <- getParams readCF2 paramRotateByteString
  paramCountSetBits <- getParams readCF1 paramCountSetBits
  paramFindFirstSetBit <- getParams readCF1 paramFindFirstSetBit
  -- And another hash function
  paramRipemd_160 <- getParams readCF1 paramRipemd_160
  -- Batch 6
  paramExpModInteger <- getParams readCF3 paramExpModInteger
  paramDropList <- getParams readCF2 paramDropList
  -- Arrays
  paramLengthOfArray <- getParams readCF1 paramLengthOfArray
  paramListToArray <- getParams readCF1 paramListToArray
  paramIndexArray <- getParams readCF2 paramIndexArray
  -- Builtin values
  paramLookupCoin <- getParams readCF3 paramLookupCoin
  paramValueContains <- getParams readCF2 paramValueContains
  paramValueData <- getParams readCF1 paramValueData
  paramUnValueData <- getParams readCF1 paramUnValueData
  paramInsertCoin <- getParams readCF4 paramInsertCoin
  paramUnionValue <- getParams readCF2 paramUnionValue
  paramScaleValue <- getParams readCF2 paramScaleValue

  pure $ BuiltinCostModelBase {..}

{- Extracting fields from R objects is a bit delicate. If you get a field name
   wrong you'll get an error message from inline-r like "Dynamic type cast
   failed. Expected: Real. Actual: Nil." from fromSEXP or "fromSEXP:Not a singleton
   vector." from dynSEXP.
-}
-- | Extract the model type descriptor from an R object
getString :: MonadR m => String -> SomeSEXP (Region m) -> m String
getString s e = fromSomeSEXP <$> [r| e_hs[[s_hs]] |]

-- | Extract the model type descriptor from an R object
getType :: MonadR m => SomeSEXP (Region m) -> m String
getType e = getString "type" e

-- | Extract the model type descriptor from an R object
getSubtype :: MonadR m => SomeSEXP (Region m) -> m String
getSubtype e = getString "subtype" e

-- | Extract a named regression coefficient from an R object
getCoeff :: MonadR m => String -> SomeSEXP (Region m) -> m CostingInteger
getCoeff f e = microToPico . fromSomeSEXP <$> [r| e_hs$model$coefficients[[f_hs]] |]

{-| Extract some other parameter from an R object.  You can add arbitrary named
parameters in mk.result in the R code and access them using this.  This can
be useful for eg, returning off-diagonal constants -}
getExtraParam :: MonadR m => String -> SomeSEXP (Region m) -> m CostingInteger
getExtraParam f e = microToPico . fromSomeSEXP <$> [r| e_hs[[f_hs]] |]

-- | For models of the form t~1: they fit a constant, but it's still called "(Intercept)"
getConstant :: MonadR m => SomeSEXP (Region m) -> m CostingInteger
getConstant = getCoeff "(Intercept)"

-- | A costing function of the form a+sx.
readOneVariableLinearFunction :: MonadR m => String -> SomeSEXP (Region m) -> m OneVariableLinearFunction
readOneVariableLinearFunction var e = do
  intercept <- Intercept <$> getCoeff "(Intercept)" e
  slope <- Slope <$> getCoeff var e
  pure $ OneVariableLinearFunction intercept slope

{-| A one-variable costing function which is constant on one region of the
plane and something else elsewhere. -}
readOneVariableFunConstOr :: MonadR m => SomeSEXP (Region m) -> m ModelConstantOrOneArgument
readOneVariableFunConstOr e = do
  constantPart <- getExtraParam "constant" e
  subtype <- getSubtype e
  nonConstantPart <- readCF1AtType subtype e
  pure $ ModelConstantOrOneArgument constantPart nonConstantPart

readOneVariableQuadraticFunction :: MonadR m => String -> SomeSEXP (Region m) -> m OneVariableQuadraticFunction
readOneVariableQuadraticFunction var e = do
  c0 <- Coefficient0 <$> getCoeff "(Intercept)" e
  c1 <- Coefficient1 <$> getCoeff (printf "I(%s)" var) e
  c2 <- Coefficient2 <$> getCoeff (printf "I(%s^2)" var) e
  pure $ OneVariableQuadraticFunction c0 c1 c2

readTwoVariableFunLinearOnDiagonal :: MonadR m => String -> SomeSEXP (Region m) -> m ModelConstantOrLinear
readTwoVariableFunLinearOnDiagonal var e = do
  constantPart <- getExtraParam "constant" e
  intercept <- Intercept <$> getCoeff "(Intercept)" e
  slope <- Slope <$> getCoeff var e
  pure $ ModelConstantOrLinear constantPart intercept slope

-- | A costing function of the form a+sx+ty
readTwoVariableLinearFunction :: MonadR m => String -> String -> SomeSEXP (Region m) -> m TwoVariableLinearFunction
readTwoVariableLinearFunction var1 var2 e = do
  intercept <- Intercept <$> getCoeff "(Intercept)" e
  slopeX <- Slope <$> getCoeff var1 e
  slopeY <- Slope <$> getCoeff var2 e
  pure $ TwoVariableLinearFunction intercept slopeX slopeY

readTwoVariableWithInteractionFunction :: MonadR m => String -> String -> SomeSEXP (Region m) -> m TwoVariableWithInteractionFunction
readTwoVariableWithInteractionFunction var1 var2 e = do
  slopeX <- Slope <$> getCoeff var1 e
  slopeY <- Slope <$> getCoeff var2 e
  slopeXY <- Slope <$> getCoeff (printf "%s:%s" var1 var2) e
  pure $ TwoVariableWithInteractionFunction slopeX slopeY slopeXY

readTwoVariableQuadraticFunction :: MonadR m => String -> String -> SomeSEXP (Region m) -> m TwoVariableQuadraticFunction
readTwoVariableQuadraticFunction var1 var2 e = do
  minVal <- getExtraParam "minimum" e
  c00 <- Coefficient00 <$> getCoeff "(Intercept)" e
  c10 <- Coefficient10 <$> getCoeff (printf "I(%s)" var1) e
  c01 <- Coefficient01 <$> getCoeff (printf "I(%s)" var2) e
  c20 <- Coefficient20 <$> getCoeff (printf "I(%s^2)" var1) e
  c11 <- Coefficient11 <$> getCoeff (printf "I(%s * %s)" var1 var2) e
  c02 <- Coefficient02 <$> getCoeff (printf "I(%s^2)" var2) e
  pure $ TwoVariableQuadraticFunction minVal c00 c10 c01 c20 c11 c02

-- Specialised version of readTwoVariableQuadraticFunction for a*YZ^2 + b*YZ
readExpModCostingFunction :: MonadR m => String -> String -> SomeSEXP (Region m) -> m ExpModCostingFunction
readExpModCostingFunction var1 var2 e = do
  c00 <- Coefficient00 <$> getCoeff "(Intercept)" e
  c11 <- Coefficient11 <$> getCoeff (printf "I(%s * %s)" var1 var2) e
  c12 <- Coefficient12 <$> getCoeff (printf "I(%s * %s^2)" var1 var2) e
  pure $ ExpModCostingFunction c00 c11 c12

{-| A two-variable costing function which is constant on one region of the
plane and something else elsewhere. -}
readTwoVariableFunConstOr :: MonadR m => SomeSEXP (Region m) -> m ModelConstantOrTwoArguments
readTwoVariableFunConstOr e = do
  constantPart <- getExtraParam "constant" e
  subtype <- getSubtype e
  nonConstantPart <- readCF2AtType subtype e
  pure $ ModelConstantOrTwoArguments constantPart nonConstantPart

{-| Functions to read CPU costing functions from R.  There are some costing
function types which are currently only used for memory models (which are
constructed directly, not via R), and those won't be handled here.  These
functions have short names to improve formatting elsewhere. -}
{-| Read in a one-variable costing function of a given type.  We have to supply
 the type as a parameter so that we can deal with nested costing functions which
 have type and subtype tags. -}
readCF1AtType :: MonadR m => String -> SomeSEXP (Region m) -> m ModelOneArgument
readCF1AtType ty e = do
  case ty of
    "constant_cost" -> ModelOneArgumentConstantCost <$> getConstant e
    "linear_in_x" -> ModelOneArgumentLinearInX <$> readOneVariableLinearFunction "x_mem" e
    _ -> error $ "Unknown one-variable model type: " ++ ty

readCF1 :: MonadR m => SomeSEXP (Region m) -> m ModelOneArgument
readCF1 e = do
  ty <- getType e
  readCF1AtType ty e

readCF2AtType :: MonadR m => String -> SomeSEXP (Region m) -> m ModelTwoArguments
readCF2AtType ty e = do
  case ty of
    "constant_cost" -> ModelTwoArgumentsConstantCost <$> getConstant e
    "linear_in_x" -> ModelTwoArgumentsLinearInX <$> readOneVariableLinearFunction "x_mem" e
    "linear_in_y" -> ModelTwoArgumentsLinearInY <$> readOneVariableLinearFunction "y_mem" e
    "linear_in_x_and_y" -> ModelTwoArgumentsLinearInXAndY <$> readTwoVariableLinearFunction "x_mem" "y_mem" e
    "added_sizes" -> ModelTwoArgumentsAddedSizes <$> readOneVariableLinearFunction "I(x_mem + y_mem)" e
    "multiplied_sizes" -> ModelTwoArgumentsMultipliedSizes <$> readOneVariableLinearFunction "I(x_mem * y_mem)" e
    "min_size" -> ModelTwoArgumentsMinSize <$> readOneVariableLinearFunction "pmin(x_mem, y_mem)" e
    "max_size" -> ModelTwoArgumentsMaxSize <$> readOneVariableLinearFunction "pmax(x_mem, y_mem)" e
    -- See Note [Backward compatibility for costing functions] for linear_on_diagonal
    "linear_on_diagonal" -> ModelTwoArgumentsLinearOnDiagonal <$> readTwoVariableFunLinearOnDiagonal "x_mem" e
    "const_below_diagonal" -> ModelTwoArgumentsConstBelowDiagonal <$> readTwoVariableFunConstOr e
    "const_above_diagonal" -> ModelTwoArgumentsConstAboveDiagonal <$> readTwoVariableFunConstOr e
    "const_off_diagonal" -> ModelTwoArgumentsConstOffDiagonal <$> readOneVariableFunConstOr e
    "quadratic_in_y" -> ModelTwoArgumentsQuadraticInY <$> readOneVariableQuadraticFunction "y_mem" e
    "quadratic_in_x_and_y" -> ModelTwoArgumentsQuadraticInXAndY <$> readTwoVariableQuadraticFunction "x_mem" "y_mem" e
    "with_interaction_in_x_and_y" -> ModelTwoArgumentsWithInteractionInXAndY <$> readTwoVariableWithInteractionFunction "x_mem" "y_mem" e
    _ -> error $ "Unknown two-variable model type: " ++ ty

readCF2 :: MonadR m => SomeSEXP (Region m) -> m ModelTwoArguments
readCF2 e = do
  ty <- getType e
  readCF2AtType ty e

readCF3 :: MonadR m => SomeSEXP (Region m) -> m ModelThreeArguments
readCF3 e = do
  ty <- getType e
  case ty of
    "constant_cost" -> ModelThreeArgumentsConstantCost <$> getConstant e
    "linear_in_x" -> ModelThreeArgumentsLinearInX <$> readOneVariableLinearFunction "x_mem" e
    "linear_in_y" -> ModelThreeArgumentsLinearInY <$> readOneVariableLinearFunction "y_mem" e
    "linear_in_z" -> ModelThreeArgumentsLinearInZ <$> readOneVariableLinearFunction "z_mem" e
    "quadratic_in_z" -> ModelThreeArgumentsQuadraticInZ <$> readOneVariableQuadraticFunction "z_mem" e
    "linear_in_y_and_z" -> ModelThreeArgumentsLinearInYAndZ <$> readTwoVariableLinearFunction "y_mem" "z_mem" e
    "literal_in_y_or_linear_in_z" -> ModelThreeArgumentsLiteralInYOrLinearInZ <$> error "literal"
    "exp_mod_cost" -> ModelThreeArgumentsExpModCost <$> readExpModCostingFunction "y_mem" "z_mem" e
    _ -> error $ "Unknown three-variable model type: " ++ ty

readCF4 :: MonadR m => SomeSEXP (Region m) -> m ModelFourArguments
readCF4 e = do
  ty <- getType e
  case ty of
    "constant_cost" -> ModelFourArgumentsConstantCost <$> getConstant e
    "linear_in_w" -> ModelFourArgumentsLinearInW <$> readOneVariableLinearFunction "w_mem" e
    _ -> error $ "Unknown four-variable model type: " ++ ty

readCF6 :: MonadR m => SomeSEXP (Region m) -> m ModelSixArguments
readCF6 e = do
  ty <- getType e
  case ty of
    "constant_cost" -> ModelSixArgumentsConstantCost <$> getConstant e
    _ -> error $ "Unknown six-variable model type: " ++ ty
