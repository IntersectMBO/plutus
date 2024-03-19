-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE RecordWildCards   #-}

module CreateBuiltinCostModel where

import PlutusCore.Crypto.BLS12_381.G1 qualified as G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as Pairing
import PlutusCore.Crypto.Hash qualified as Hash
import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.CostStream
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Machine.ExMemoryUsage

import Barbies (bmap, bsequence)
import Control.Applicative (Const (Const, getConst))
-- import Control.Exception (TypeError (TypeError))
-- import Control.Monad.Catch (throwM)
import Data.Coerce (coerce)
import Data.Functor.Compose (Compose (Compose))
import Data.SatInt
import Data.Text (Text)
import Text.Printf (printf)

import H.Prelude (MonadR, Region)
import Language.R (SomeSEXP, defaultConfig, fromSomeSEXP, runRegion, withEmbeddedR)
import Language.R.QQ (r)

-- | Convert microseconds represented as a float to picoseconds represented as a
-- CostingInteger.  We round up to be sure we don't underestimate anything.
microToPico :: Double -> CostingInteger
microToPico = unsafeToSatInt . ceiling . (1e6 *)

{- See CostModelGeneration.md for a description of what this does. -}

-- TODO some generics magic.
-- Mentioned in CostModel.md. Change here, change there.
-- The names of the models in R.
-- If you get one of these wrong you'll probably get a message saying
-- 'parse error (not enough input) at ""'.
builtinCostModelNames :: BuiltinCostModelBase (Const Text)
builtinCostModelNames = BuiltinCostModelBase
  { paramAddInteger                      = "addIntegerModel"
  , paramSubtractInteger                 = "subtractIntegerModel"
  , paramMultiplyInteger                 = "multiplyIntegerModel"
  , paramDivideInteger                   = "divideIntegerModel"
  , paramQuotientInteger                 = "quotientIntegerModel"
  , paramRemainderInteger                = "remainderIntegerModel"
  , paramModInteger                      = "modIntegerModel"
  , paramEqualsInteger                   = "equalsIntegerModel"
  , paramLessThanInteger                 = "lessThanIntegerModel"
  , paramLessThanEqualsInteger           = "lessThanEqualsIntegerModel"
  , paramAppendByteString                = "appendByteStringModel"
  , paramConsByteString                  = "consByteStringModel"
  , paramSliceByteString                 = "sliceByteStringModel"
  , paramLengthOfByteString              = "lengthOfByteStringModel"
  , paramIndexByteString                 = "indexByteStringModel"
  , paramEqualsByteString                = "equalsByteStringModel"
  , paramLessThanByteString              = "lessThanByteStringModel"
  , paramLessThanEqualsByteString        = "lessThanEqualsByteStringModel"
  , paramSha2_256                        = "sha2_256Model"
  , paramSha3_256                        = "sha3_256Model"
  , paramBlake2b_256                     = "blake2b_256Model"
  , paramVerifyEd25519Signature          = "verifyEd25519SignatureModel"
  , paramVerifyEcdsaSecp256k1Signature   = "verifyEcdsaSecp256k1SignatureModel"
  , paramVerifySchnorrSecp256k1Signature = "verifySchnorrSecp256k1SignatureModel"
  , paramAppendString                    = "appendStringModel"
  , paramEqualsString                    = "equalsStringModel"
  , paramEncodeUtf8                      = "encodeUtf8Model"
  , paramDecodeUtf8                      = "decodeUtf8Model"
  , paramIfThenElse                      = "ifThenElseModel"
  , paramChooseUnit                      = "chooseUnitModel"
  , paramTrace                           = "traceModel"
  , paramFstPair                         = "fstPairModel"
  , paramSndPair                         = "sndPairModel"
  , paramChooseList                      = "chooseListModel"
  , paramMkCons                          = "mkConsModel"
  , paramHeadList                        = "headListModel"
  , paramTailList                        = "tailListModel"
  , paramNullList                        = "nullListModel"
  , paramChooseData                      = "chooseDataModel"
  , paramConstrData                      = "constrDataModel"
  , paramMapData                         = "mapDataModel"
  , paramListData                        = "listDataModel"
  , paramIData                           = "iDataModel"
  , paramBData                           = "bDataModel"
  , paramUnConstrData                    = "unConstrDataModel"
  , paramUnMapData                       = "unMapDataModel"
  , paramUnListData                      = "unListDataModel"
  , paramUnIData                         = "unIDataModel"
  , paramUnBData                         = "unBDataModel"
  , paramEqualsData                      = "equalsDataModel"
  , paramMkPairData                      = "mkPairDataModel"
  , paramMkNilData                       = "mkNilDataModel"
  , paramMkNilPairData                   = "mkNilPairDataModel"
  , paramSerialiseData                   = "serialiseDataModel"
  , paramBls12_381_G1_add                = "bls12_381_G1_addModel"
  , paramBls12_381_G1_neg                = "bls12_381_G1_negModel"
  , paramBls12_381_G1_scalarMul          = "bls12_381_G1_scalarMulModel"
  , paramBls12_381_G1_equal              = "bls12_381_G1_equalModel"
  , paramBls12_381_G1_compress           = "bls12_381_G1_compressModel"
  , paramBls12_381_G1_uncompress         = "bls12_381_G1_uncompressModel"
  , paramBls12_381_G1_hashToGroup        = "bls12_381_G1_hashToGroupModel"
  , paramBls12_381_G2_add                = "bls12_381_G2_addModel"
  , paramBls12_381_G2_neg                = "bls12_381_G2_negModel"
  , paramBls12_381_G2_scalarMul          = "bls12_381_G2_scalarMulModel"
  , paramBls12_381_G2_equal              = "bls12_381_G2_equalModel"
  , paramBls12_381_G2_compress           = "bls12_381_G2_compressModel"
  , paramBls12_381_G2_uncompress         = "bls12_381_G2_uncompressModel"
  , paramBls12_381_G2_hashToGroup        = "bls12_381_G2_hashToGroupModel"
  , paramBls12_381_millerLoop            = "bls12_381_millerLoopModel"
  , paramBls12_381_mulMlResult           = "bls12_381_mulMlResultModel"
  , paramBls12_381_finalVerify           = "bls12_381_finalVerifyModel"
  , paramBlake2b_224                     = "blake2b_224Model"
  , paramKeccak_256                      = "keccak_256Model"
  , paramIntegerToByteString             = "integerToByteStringModel"
  , paramByteStringToInteger             = "byteStringToIntegerModel"
  }


-- | Loads the models from R.
-- The "_hs" suffixes below make Haskell variables accessible inside [r| ... |]
costModelsR :: MonadR m =>
  FilePath
  -> FilePath
  -> m (BuiltinCostModelBase (Const (SomeSEXP (Region m))))
costModelsR bmfile rfile = do
  list <- [r|
             source(rfile_hs)
             modelFun(bmfile_hs)
           |]
  let makeCostModelEntry name =
          let n = getConst name
          in Compose $ fmap Const $ [r| list_hs [[n_hs]] |]
  bsequence $ bmap makeCostModelEntry builtinCostModelNames

-- | Creates the cost model from a CSV benchmarking results file and a file
-- containing R modelling code.
createBuiltinCostModel :: FilePath -> FilePath -> IO BuiltinCostModel
createBuiltinCostModel bmfile rfile = do
  withEmbeddedR defaultConfig $ runRegion $ do
    models <- costModelsR bmfile rfile
    let getParams x y = x (getConst $ y models)

    -- Integers
    paramAddInteger                      <- getParams addInteger                paramAddInteger
    paramSubtractInteger                 <- getParams subtractInteger           paramSubtractInteger
    paramMultiplyInteger                 <- getParams multiplyInteger           paramMultiplyInteger
    paramDivideInteger                   <- getParams divideInteger             paramDivideInteger
    paramQuotientInteger                 <- getParams quotientInteger           paramQuotientInteger
    paramRemainderInteger                <- getParams remainderInteger          paramRemainderInteger
    paramModInteger                      <- getParams modInteger                paramModInteger
    paramEqualsInteger                   <- getParams equalsInteger             paramEqualsInteger
    paramLessThanInteger                 <- getParams lessThanInteger           paramLessThanInteger
    paramLessThanEqualsInteger           <- getParams lessThanEqualsInteger     paramLessThanEqualsInteger
    -- Bytestrings
    paramAppendByteString                <- getParams appendByteString          paramAppendByteString
    paramConsByteString                  <- getParams consByteString            paramConsByteString
    paramSliceByteString                 <- getParams sliceByteString           paramSliceByteString
    paramLengthOfByteString              <- getParams lengthOfByteString        paramLengthOfByteString
    paramIndexByteString                 <- getParams indexByteString           paramIndexByteString
    paramEqualsByteString                <- getParams equalsByteString          paramEqualsByteString
    paramLessThanByteString              <- getParams lessThanByteString        paramLessThanByteString
    paramLessThanEqualsByteString        <- getParams lessThanEqualsByteString  paramLessThanEqualsByteString
    -- Cryptography and hashes
    paramSha2_256                        <- getParams sha2_256                         paramSha2_256
    paramSha3_256                        <- getParams sha3_256                         paramSha3_256
    paramBlake2b_256                     <- getParams blake2b_256                      paramBlake2b_256
    paramVerifyEd25519Signature          <- getParams verifyEd25519Signature           paramVerifyEd25519Signature
    paramVerifyEcdsaSecp256k1Signature   <- getParams verifyEcdsaSecp256k1Signature    paramVerifyEcdsaSecp256k1Signature
    paramVerifySchnorrSecp256k1Signature <- getParams verifySchnorrSecp256k1Signature  paramVerifySchnorrSecp256k1Signature
    -- Strings
    paramAppendString                    <- getParams appendString  paramAppendString
    paramEqualsString                    <- getParams equalsString  paramEqualsString
    paramEncodeUtf8                      <- getParams encodeUtf8    paramEncodeUtf8
    paramDecodeUtf8                      <- getParams decodeUtf8    paramDecodeUtf8
    -- Bool
    paramIfThenElse                      <- getParams ifThenElse  paramIfThenElse
    -- Unit
    paramChooseUnit                      <- getParams chooseUnit  paramChooseUnit
    -- Tracing
    paramTrace                           <- getParams trace       paramTrace
    -- Pairs
    paramFstPair                         <- getParams fstPair     paramFstPair
    paramSndPair                         <- getParams sndPair     paramSndPair
    -- Lists
    paramChooseList                      <- getParams chooseList  paramChooseList
    paramMkCons                          <- getParams mkCons      paramMkCons
    paramHeadList                        <- getParams headList    paramHeadList
    paramTailList                        <- getParams tailList    paramTailList
    paramNullList                        <- getParams nullList    paramNullList
    -- Data
    paramChooseData                      <- getParams chooseData     paramChooseData
    paramConstrData                      <- getParams constrData     paramConstrData
    paramMapData                         <- getParams mapData        paramMapData
    paramListData                        <- getParams listData       paramListData
    paramIData                           <- getParams iData          paramIData
    paramBData                           <- getParams bData          paramBData
    paramUnConstrData                    <- getParams unConstrData   paramUnConstrData
    paramUnMapData                       <- getParams unMapData      paramUnMapData
    paramUnListData                      <- getParams unListData     paramUnListData
    paramUnIData                         <- getParams unIData        paramUnIData
    paramUnBData                         <- getParams unBData        paramUnBData
    paramEqualsData                      <- getParams equalsData     paramEqualsData
    paramSerialiseData                   <- getParams serialiseData  paramSerialiseData
    -- Misc constructors
    paramMkPairData                      <- getParams mkPairData     paramMkPairData
    paramMkNilData                       <- getParams mkNilData      paramMkNilData
    paramMkNilPairData                   <- getParams mkNilPairData  paramMkNilPairData
    -- BLS12-381
    paramBls12_381_G1_add                <- getParams bls12_381_G1_add          paramBls12_381_G1_add
    paramBls12_381_G1_neg                <- getParams bls12_381_G1_neg          paramBls12_381_G1_neg
    paramBls12_381_G1_scalarMul          <- getParams bls12_381_G1_scalarMul    paramBls12_381_G1_scalarMul
    paramBls12_381_G1_equal              <- getParams bls12_381_G1_equal        paramBls12_381_G1_equal
    paramBls12_381_G1_compress           <- getParams bls12_381_G1_compress     paramBls12_381_G1_compress
    paramBls12_381_G1_uncompress         <- getParams bls12_381_G1_uncompress   paramBls12_381_G1_uncompress
    paramBls12_381_G1_hashToGroup        <- getParams bls12_381_G1_hashToGroup  paramBls12_381_G1_hashToGroup
    paramBls12_381_G2_add                <- getParams bls12_381_G2_add          paramBls12_381_G2_add
    paramBls12_381_G2_neg                <- getParams bls12_381_G2_neg          paramBls12_381_G2_neg
    paramBls12_381_G2_scalarMul          <- getParams bls12_381_G2_scalarMul    paramBls12_381_G2_scalarMul
    paramBls12_381_G2_equal              <- getParams bls12_381_G2_equal        paramBls12_381_G2_equal
    paramBls12_381_G2_compress           <- getParams bls12_381_G2_compress     paramBls12_381_G2_compress
    paramBls12_381_G2_uncompress         <- getParams bls12_381_G2_uncompress   paramBls12_381_G2_uncompress
    paramBls12_381_G2_hashToGroup        <- getParams bls12_381_G2_hashToGroup  paramBls12_381_G2_hashToGroup
    paramBls12_381_millerLoop            <- getParams bls12_381_millerLoop      paramBls12_381_millerLoop
    paramBls12_381_mulMlResult           <- getParams bls12_381_mulMlResult     paramBls12_381_mulMlResult
    paramBls12_381_finalVerify           <- getParams bls12_381_finalVerify     paramBls12_381_finalVerify
    -- More hashes
    paramKeccak_256                      <- getParams keccak_256                paramKeccak_256
    paramBlake2b_224                     <- getParams blake2b_224               paramBlake2b_224
    -- Bitwise operations
    paramByteStringToInteger             <- getParams byteStringToInteger       paramByteStringToInteger
    paramIntegerToByteString             <- getParams integerToByteString       paramIntegerToByteString

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
getCoeff f e = microToPico . fromSomeSEXP  <$> [r| e_hs$model$coefficients[[f_hs]] |]

-- | Extract some other parameter from an R object.  You can add arbitrary named
-- parameters in mk.result in the R code and access them using this.  This can
-- be useful for eg, returning off-diagonal constants
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

-- | A costing function of the form a+sx.
readOneVariableQuadraticFunction :: MonadR m => String -> SomeSEXP (Region m) -> m OneVariableQuadraticFunction
readOneVariableQuadraticFunction var e = do
  coeff0 <- Coefficient0 <$> getCoeff "(Intercept)" e
  coeff1 <- Coefficient1 <$> getCoeff (printf "I(%s)" var) e
  coeff2 <- Coefficient2 <$> getCoeff (printf "I(%s^2)" var) e
  pure $ OneVariableQuadraticFunction coeff0 coeff1 coeff2

-- | A costing function of the form a+sx+ty
readTwoVariableLinearFunction :: MonadR m => String -> String -> SomeSEXP (Region m) -> m TwoVariableLinearFunction
readTwoVariableLinearFunction var1 var2 e = do
  intercept <- Intercept <$> getCoeff "(Intercept)" e
  slopeX <- Slope <$> getCoeff var1 e
  slopeY <- Slope <$> getCoeff var2 e
  pure $ TwoVariableLinearFunction intercept slopeX slopeY

-- | A two-variable costing function which is constant on one region of the
-- plane and linear in one variable elsewhere.  TODO: generalise from a linear
-- function to a general function.  This would change the JSON nesting.
readTwoVariableFunConstOrLinear :: MonadR m => String -> SomeSEXP (Region m) -> m ModelConstantOrLinear
readTwoVariableFunConstOrLinear var e = do
  constantPart <- getExtraParam "const" e
  intercept <- Intercept <$> getCoeff "(Intercept)" e
  slope <- Slope <$> getCoeff var e
  pure $ ModelConstantOrLinear constantPart intercept slope

-- | A two-variable costing function which is constant on one region of the
-- plane and something else elsewhere.
readTwoVariableFunConstOr :: MonadR m => SomeSEXP (Region m) -> m ModelConstantOrTwoArguments
readTwoVariableFunConstOr e = do
  constantPart <- getExtraParam "const" e
  subtype <- getSubtype e
  nonConstantPart <- loadTwoVariableCostingFunctionOfType subtype e
  pure $ ModelConstantOrTwoArguments constantPart nonConstantPart

-- | Functions to read CPU costing functions from R.  There are some costing
-- function types which are currently only used for memory models (which are
-- constructed directly, not via R), and those won't be handled here.

loadOneVariableCostingFunction :: MonadR m => SomeSEXP (Region m) -> m ModelOneArgument
loadOneVariableCostingFunction e = do
  ty <- getType e
  case ty of
    "constant_cost" -> ModelOneArgumentConstantCost <$> getConstant e
    "linear_cost"   -> ModelOneArgumentLinearCost <$> readOneVariableLinearFunction "x_mem" e
    "linear_in_x"   -> ModelOneArgumentLinearCost <$> readOneVariableLinearFunction "x_mem" e  -- FIXME: duplicate
    _               -> error $ "Unknown one-variable model type: " ++ ty

-- | Load in a two-variable costing function of a given type.  We have to supply
-- the type as a parameter so that we can deal with nested costing functions
-- which have type and subtype tags.  This generality is currently only required
-- for two-variable costing functions.
loadTwoVariableCostingFunctionOfType :: MonadR m => String -> SomeSEXP (Region m) -> m ModelTwoArguments
loadTwoVariableCostingFunctionOfType ty e = do
  case ty of
    "constant_cost"        -> ModelTwoArgumentsConstantCost       <$> getConstant e
    "linear_in_x"          -> ModelTwoArgumentsLinearInX          <$> readOneVariableLinearFunction "x_mem" e
    "linear_in_y"          -> ModelTwoArgumentsLinearInY          <$> readOneVariableLinearFunction "y_mem" e
    "linear_in_x_and_y"    -> ModelTwoArgumentsLinearInXAndY      <$> readTwoVariableLinearFunction "x_mem" "y_mem" e
    "added_sizes"          -> ModelTwoArgumentsAddedSizes         <$> readOneVariableLinearFunction "I(x_mem + y_mem)" e
    "multiplied_sizes"     -> ModelTwoArgumentsMultipliedSizes    <$> readOneVariableLinearFunction "I(x_mem * y_mem)" e
    "min_size"             -> ModelTwoArgumentsMinSize            <$> readOneVariableLinearFunction "pmin(x_mem, y_mem)" e
    "max_size"             -> ModelTwoArgumentsMaxSize            <$> readOneVariableLinearFunction "pmax(x_mem, y_mem)" e
    "linear_on_diagonal"   -> ModelTwoArgumentsLinearOnDiagonal   <$> readTwoVariableFunConstOrLinear "x_mem" e
    "const_below_diagonal" -> ModelTwoArgumentsConstBelowDiagonal <$> readTwoVariableFunConstOr e
    "const_above_diagonal" -> ModelTwoArgumentsConstAboveDiagonal <$> readTwoVariableFunConstOr e
    "quadratic_in_y"       -> ModelTwoArgumentsQuadraticInY       <$> readOneVariableQuadraticFunction "y_mem" e
    _                      -> error $ "Unknown two-variable model type: " ++ ty

loadTwoVariableCostingFunction :: MonadR m => SomeSEXP (Region m) -> m ModelTwoArguments
loadTwoVariableCostingFunction e = do
  ty <- getType e
  loadTwoVariableCostingFunctionOfType ty e

loadThreeVariableCostingFunction :: MonadR m => SomeSEXP (Region m) -> m ModelThreeArguments
loadThreeVariableCostingFunction e = do
  ty <- getType e
  case ty of
    "constant_cost"               -> ModelThreeArgumentsConstantCost          <$> getConstant e
    "linear_in_x"                 -> ModelThreeArgumentsLinearInX             <$> readOneVariableLinearFunction "x_mem" e
    "linear_in_y"                 -> ModelThreeArgumentsLinearInY             <$> readOneVariableLinearFunction "y_mem" e
    "linear_in_z"                 -> ModelThreeArgumentsLinearInZ             <$> readOneVariableLinearFunction "z_mem" e
    "quadratic_in_z"              -> ModelThreeArgumentsQuadraticInZ          <$> readOneVariableQuadraticFunction "z_mem" e
    "literal_in_y_or_linear_in_z" -> ModelThreeArgumentsLiteralInYOrLinearInZ <$> error "literal"
    _                             -> error $ "Unknown three-variable model type: " ++ ty

loadSixVariableCostingFunction :: MonadR m => SomeSEXP (Region m) -> m ModelSixArguments
loadSixVariableCostingFunction e = do
  ty <- getType e
  case ty of
    "constant_cost" -> ModelSixArgumentsConstantCost <$> getConstant e
    _               -> error $ "Unknown six-variable model type: " ++ ty

boolMemModel :: ModelTwoArguments
boolMemModel = ModelTwoArgumentsConstantCost 1

memoryUsageAsCostingInteger :: ExMemoryUsage a => a -> CostingInteger
memoryUsageAsCostingInteger = coerce . sumCostStream . flattenCostRose . memoryUsage

-- | The types of functions which take an R SEXP and extract a CPU model from
-- it, then pair it up with a memory costing function.
type MakeCostingFun1 = forall m . MonadR m => SomeSEXP (Region m) -> m (CostingFun ModelOneArgument)
type MakeCostingFun2 = forall m . MonadR m => SomeSEXP (Region m) -> m (CostingFun ModelTwoArguments)
type MakeCostingFun3 = forall m . MonadR m => SomeSEXP (Region m) -> m (CostingFun ModelThreeArguments)
type MakeCostingFun6 = forall m . MonadR m => SomeSEXP (Region m) -> m (CostingFun ModelSixArguments)

-- | Create a
makeOneVariableCostingFunction :: ModelOneArgument -> MakeCostingFun1
makeOneVariableCostingFunction memModel e =
  CostingFun <$> (loadOneVariableCostingFunction e) <*> pure memModel

makeTwoVariableCostingFunction :: ModelTwoArguments -> MakeCostingFun2
makeTwoVariableCostingFunction memModel e =
  CostingFun <$> (loadTwoVariableCostingFunction e) <*> pure memModel

makeThreeVariableCostingFunction :: ModelThreeArguments -> MakeCostingFun3
makeThreeVariableCostingFunction memModel e =
  CostingFun <$> (loadThreeVariableCostingFunction e) <*> pure memModel

makeSixVariableCostingFunction :: ModelSixArguments -> MakeCostingFun6
makeSixVariableCostingFunction memModel e =
  CostingFun <$> (loadSixVariableCostingFunction e) <*> pure memModel

---------------- Integers ----------------

addInteger :: MakeCostingFun2
addInteger =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsMaxSize $ OneVariableLinearFunction 1 1

subtractInteger :: MakeCostingFun2
subtractInteger =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsMaxSize $ OneVariableLinearFunction 1 1
  -- The worst case is subtracting e.g. `minBound :: Int` - `maxBound :: Int`, which increases the memory usage by one.
  -- (max x y) + 1

multiplyInteger :: MakeCostingFun2
multiplyInteger =
  -- GMP requires multiplication (mpn_mul) to have x + y space.
  -- x + y
  makeTwoVariableCostingFunction $ ModelTwoArgumentsAddedSizes $ OneVariableLinearFunction 0 1

divideInteger :: MakeCostingFun2
divideInteger =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsSubtractedSizes $ ModelSubtractedSizes 0 1 1

quotientInteger :: MakeCostingFun2
quotientInteger =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsSubtractedSizes $ ModelSubtractedSizes 0 1 1

remainderInteger :: MakeCostingFun2
remainderInteger = quotientInteger

modInteger :: MakeCostingFun2
modInteger = divideInteger

-- FIXME: should probably be piecewise (harmless, but may overprice some comparisons a bit)
equalsInteger :: MakeCostingFun2
equalsInteger =
  makeTwoVariableCostingFunction boolMemModel

lessThanInteger :: MakeCostingFun2
lessThanInteger =
  makeTwoVariableCostingFunction boolMemModel

lessThanEqualsInteger :: MakeCostingFun2
lessThanEqualsInteger =
  makeTwoVariableCostingFunction boolMemModel


---------------- Bytestrings ----------------

appendByteString :: MakeCostingFun2
appendByteString =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsAddedSizes $ OneVariableLinearFunction 0 1

consByteString :: MakeCostingFun2
consByteString =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsAddedSizes $ OneVariableLinearFunction 0 1


{- | Return a substring of a bytestring with a specified start point and length.
   Plutus Core bytestrings are implemented using Data.ByteString, which
   represents a (strict) bytestring as a C array of bytes together with a
   pointer into that and a length.  The sliceByteString function is implemented
   using 'take' and 'drop', and these work by modifying the pointer and length:
   no bytes are copied so sliceByteString requires constant time and a constant
   memory overhead.  There's a mismatch here because the Haskell model which we
   defined for SliceByteString is linear in the length of the bytestring;
   however we can still use that to model the constant cost inferred in the R
   code.
-}
sliceByteString :: MakeCostingFun3
sliceByteString =
  makeThreeVariableCostingFunction $ ModelThreeArgumentsLinearInZ $ OneVariableLinearFunction 4 0

lengthOfByteString :: MakeCostingFun1
lengthOfByteString =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 10

indexByteString :: MakeCostingFun2
indexByteString =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsConstantCost 4

equalsByteString :: MakeCostingFun2
equalsByteString =
  makeTwoVariableCostingFunction $ boolMemModel

lessThanByteString :: MakeCostingFun2
lessThanByteString =
  makeTwoVariableCostingFunction boolMemModel

lessThanEqualsByteString :: MakeCostingFun2
lessThanEqualsByteString = lessThanByteString


---------------- Cryptography and hashes ----------------

sha2_256 :: MakeCostingFun1
sha2_256 =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost hashSize
  where hashSize = memoryUsageAsCostingInteger $ Hash.sha2_256 ""

sha3_256 :: MakeCostingFun1
sha3_256 =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost hashSize
  where hashSize = memoryUsageAsCostingInteger $ Hash.sha3_256 ""

blake2b_224 :: MakeCostingFun1
blake2b_224 =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost hashSize
  where hashSize = memoryUsageAsCostingInteger $ Hash.blake2b_224 ""

blake2b_256 :: MakeCostingFun1
blake2b_256 =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost hashSize
  where hashSize = memoryUsageAsCostingInteger $ Hash.blake2b_256 ""

keccak_256 :: MakeCostingFun1
keccak_256 =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost hashSize
  where hashSize = memoryUsageAsCostingInteger $ Hash.keccak_256 ""


-- NB: the R model is based purely on the size of the second argument (since the
-- first and third are constant size), so we have to rearrange things a bit to
-- get it to work with a three-argument costing function.
verifyEd25519Signature :: MakeCostingFun3
verifyEd25519Signature =
  makeThreeVariableCostingFunction $ ModelThreeArgumentsConstantCost 10

verifyEcdsaSecp256k1Signature :: MakeCostingFun3
verifyEcdsaSecp256k1Signature =
  makeThreeVariableCostingFunction $ ModelThreeArgumentsConstantCost 10

verifySchnorrSecp256k1Signature :: MakeCostingFun3
verifySchnorrSecp256k1Signature =
  makeThreeVariableCostingFunction $ ModelThreeArgumentsConstantCost 10

---------------- Strings ----------------

appendString :: MakeCostingFun2
appendString =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsAddedSizes $ OneVariableLinearFunction 4 1

equalsString :: MakeCostingFun2
equalsString =
  makeTwoVariableCostingFunction boolMemModel

encodeUtf8 :: MakeCostingFun1
encodeUtf8 =
  makeOneVariableCostingFunction $ ModelOneArgumentLinearCost $ OneVariableLinearFunction 4 2
  -- In the worst case two UTF-16 bytes encode to three UTF-8
  -- bytes, so two output words per input word should cover that.

decodeUtf8 :: MakeCostingFun1
decodeUtf8 =
  makeOneVariableCostingFunction $ ModelOneArgumentLinearCost $ OneVariableLinearFunction 4 2
  -- In the worst case one UTF-8 byte decodes to two UTF-16 bytes

---------------- Bool ----------------
ifThenElse :: MakeCostingFun3
ifThenElse =
  makeThreeVariableCostingFunction $ ModelThreeArgumentsConstantCost 1

---------------- Unit ----------------

chooseUnit :: MakeCostingFun2
chooseUnit =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsConstantCost 4
-- \() a -> a

---------------- Tracing ----------------

trace :: MakeCostingFun2
trace =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsConstantCost 32

---------------- Pairs ----------------

fstPair :: MakeCostingFun1
fstPair =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- (x,_) -> x; but with lots of Some's etc.

sndPair :: MakeCostingFun1
sndPair =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- (_,y) -> y; but with lots of Some's etc.

---------------- Lists ----------------

chooseList :: MakeCostingFun3
chooseList =
  makeThreeVariableCostingFunction $ ModelThreeArgumentsConstantCost 32
-- xs a b -> a if xs == [], b otherwise

mkCons :: MakeCostingFun2
mkCons =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsConstantCost 32
-- x xs -> x:xs, but with a dynamic type check

headList :: MakeCostingFun1
headList =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- x:_ -> x, [] -> failure.  Successful case has fromValueOf etc.

tailList :: MakeCostingFun1
tailList =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- Like headList

nullList :: MakeCostingFun1
nullList =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- x::[a] -> Bool

---------------- Data ----------------

chooseData :: MakeCostingFun6
chooseData =
  makeSixVariableCostingFunction $ ModelSixArgumentsConstantCost 32
-- chooseData d p q r s t u  returns one of the last six elements according to what d is.

constrData :: MakeCostingFun2
constrData =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsConstantCost 32
-- Just applying Constr

mapData :: MakeCostingFun1
mapData =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- Just applying Map

listData :: MakeCostingFun1
listData =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- Just applying List

iData :: MakeCostingFun1
iData =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- Just applying I

bData :: MakeCostingFun1
bData =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- Just applying B

unConstrData :: MakeCostingFun1
unConstrData =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- Constr i ds -> (i,ds);  _ -> fail

unMapData :: MakeCostingFun1
unMapData =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- Map es -> es;  _ -> fail

unListData :: MakeCostingFun1
unListData =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- List ds -> ds;  _ -> fail

unIData :: MakeCostingFun1
unIData =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- I i -> i;  _ -> fail

unBData :: MakeCostingFun1
unBData =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- B b -> b;  _ -> fail

equalsData :: MakeCostingFun2
equalsData =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsConstantCost 1
  {- The size function for 'Data' counts the total number of nodes, and so is
     potentially expensive.  Luckily laziness in the costing functions ensures
     that it's only called if really necessary, so it'll be called here but not
     in 'unBData' etc.  Doing the full traversal seems to increase validation times
     by one or two percent, but we can't really avoid it here. -}
  {- Note that the R code constructs this model in a non-standard way and then
     returns a model that has been modified to look like a model for minimum sizes
     so we can read it easily here. -}
  {- Another complication is that 'equalsData' will always return False when the
     arguments are of different size, but it's not clever enough to realise that
     and return immediately, so it may perform a lot of computation even off the
     diagonal.  The R model is generated from data on the diagonal, so we read
     that in here and adjust it to be linear in 'min x_mem y_mem', since in the
     worst case it may have to examine almost all of the smaller argument before
     realising that the two arguments are different. -}

serialiseData :: MakeCostingFun1
serialiseData =
  makeOneVariableCostingFunction $ ModelOneArgumentLinearCost $ OneVariableLinearFunction 0 2

---------------- Misc constructors ----------------

mkPairData :: MakeCostingFun2
mkPairData =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsConstantCost 32
-- a b -> (a,b)

mkNilData :: MakeCostingFun1
mkNilData =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- () -> [] :: [Data]

mkNilPairData :: MakeCostingFun1
mkNilPairData =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost 32
-- () -> [] :: [(Data,Data)]

---------------- BLS12_381 operations ----------------

toMemSize :: Int -> CostingInteger
toMemSize n = fromIntegral $ n `div` 8

-- Group order is 255 bits -> 32 bytes (4 words).
-- Field size is 381 bits  -> 48 bytes (6 words)
-- (with three spare bits used for encoding purposes).

-- Sizes below from sizePoint, compressedSizePoint, and sizePT in
-- Crypto.EllipticCurve.BLS12_381.Internal

-- In-memory G1 points take up 144 bytes (18 words).
-- These are projective points, so we have *three* 48-byte coordinates.
g1MemSize :: CostingInteger
g1MemSize = toMemSize G1.memSizeBytes

-- Compressed G1 points take up 48 bytes (6 words)
g1CompressedSize :: CostingInteger
g1CompressedSize = toMemSize G1.compressedSizeBytes

-- In-memory G2 points take up 288 bytes (36 words)
g2MemSize :: CostingInteger
g2MemSize = toMemSize G2.memSizeBytes

-- Compressed G2 points take up 96 bytes (12 words)
g2CompressedSize :: CostingInteger
g2CompressedSize = toMemSize G2.compressedSizeBytes

-- In-memory G2 points take up 576 bytes (72 words)
mlResultMemSize :: CostingInteger
mlResultMemSize = toMemSize Pairing.mlResultMemSizeBytes

bls12_381_G1_add :: MakeCostingFun2
bls12_381_G1_add =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsConstantCost g1MemSize

bls12_381_G1_neg :: MakeCostingFun1
bls12_381_G1_neg =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost g1MemSize

bls12_381_G1_scalarMul :: MakeCostingFun2
bls12_381_G1_scalarMul =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsConstantCost g1MemSize

bls12_381_G1_equal :: MakeCostingFun2
bls12_381_G1_equal =
  makeTwoVariableCostingFunction boolMemModel

bls12_381_G1_hashToGroup :: MakeCostingFun2
bls12_381_G1_hashToGroup =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsConstantCost g1MemSize

bls12_381_G1_compress :: MakeCostingFun1
bls12_381_G1_compress =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost g1CompressedSize

bls12_381_G1_uncompress :: MakeCostingFun1
bls12_381_G1_uncompress =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost g1MemSize

bls12_381_G2_add :: MakeCostingFun2
bls12_381_G2_add = makeTwoVariableCostingFunction $ ModelTwoArgumentsConstantCost g2MemSize

bls12_381_G2_neg :: MakeCostingFun1
bls12_381_G2_neg =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost g2MemSize

bls12_381_G2_scalarMul :: MakeCostingFun2
bls12_381_G2_scalarMul =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsConstantCost g2MemSize

bls12_381_G2_equal :: MakeCostingFun2
bls12_381_G2_equal =
  makeTwoVariableCostingFunction boolMemModel

bls12_381_G2_hashToGroup :: MakeCostingFun2
bls12_381_G2_hashToGroup  =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsConstantCost g2MemSize

bls12_381_G2_compress :: MakeCostingFun1
bls12_381_G2_compress =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost g2CompressedSize

bls12_381_G2_uncompress :: MakeCostingFun1
bls12_381_G2_uncompress =
  makeOneVariableCostingFunction $ ModelOneArgumentConstantCost g2MemSize

bls12_381_millerLoop :: MakeCostingFun2
bls12_381_millerLoop =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsConstantCost mlResultMemSize

bls12_381_mulMlResult :: MakeCostingFun2
bls12_381_mulMlResult =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsConstantCost mlResultMemSize

bls12_381_finalVerify :: MakeCostingFun2
bls12_381_finalVerify =
  makeTwoVariableCostingFunction boolMemModel

---------------- Bitwise operations ----------------

{-  Note that if we give `integerToByteString` a width argument w > 0 and a small
integer n to be converted, the cost is based only on the size of n even though w
could be considerably larger and some work will be required to pad the output to
width w.  Experiments show that the padding cost is negligible in comparison to
the conversion cost, so it's safe to base the cost purely on the size of n.
-}
integerToByteString :: MakeCostingFun3
integerToByteString =
  makeThreeVariableCostingFunction $ ModelThreeArgumentsLiteralInYOrLinearInZ $ OneVariableLinearFunction 0 1

byteStringToInteger :: MakeCostingFun2
byteStringToInteger =
  makeTwoVariableCostingFunction $ ModelTwoArgumentsLinearInY $ OneVariableLinearFunction 0 1
