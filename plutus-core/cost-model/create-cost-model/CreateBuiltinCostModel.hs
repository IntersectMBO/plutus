-- editorconfig-checker-disable-file
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}

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
import Data.ByteString (ByteString)
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
costModelsR
  :: MonadR m
  => FilePath
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
createBuiltinCostModel bmfile rfile =
  withEmbeddedR defaultConfig $ runRegion $ do
    cpuModels <- costModelsR bmfile rfile
    let
      getParams readCF param1 param2 = do
        let memModel = getId $ param1 builtinMemModels
        cpuModel <- readCF $ getConst $ param2 cpuModels
        pure $ CostingFun cpuModel memModel

    -- Integers
    paramAddInteger                      <- getParams lcf2 paramAddInteger             paramAddInteger
    paramSubtractInteger                 <- getParams lcf2 paramSubtractInteger        paramSubtractInteger
    paramMultiplyInteger                 <- getParams lcf2 paramMultiplyInteger        paramMultiplyInteger
    paramDivideInteger                   <- getParams lcf2 paramDivideInteger          paramDivideInteger
    paramQuotientInteger                 <- getParams lcf2 paramQuotientInteger        paramQuotientInteger
    paramRemainderInteger                <- getParams lcf2 paramRemainderInteger       paramRemainderInteger
    paramModInteger                      <- getParams lcf2 paramModInteger             paramModInteger
    paramEqualsInteger                   <- getParams lcf2 paramEqualsInteger          paramEqualsInteger
    paramLessThanInteger                 <- getParams lcf2 paramLessThanInteger        paramLessThanInteger
    paramLessThanEqualsInteger           <- getParams lcf2 paramLessThanEqualsInteger  paramLessThanEqualsInteger
    -- Bytestrings
    paramAppendByteString                <- getParams lcf2 paramAppendByteString          paramAppendByteString
    paramConsByteString                  <- getParams lcf2 paramConsByteString            paramConsByteString
    paramSliceByteString                 <- getParams lcf3 paramSliceByteString           paramSliceByteString
    paramLengthOfByteString              <- getParams lcf1 paramLengthOfByteString        paramLengthOfByteString
    paramIndexByteString                 <- getParams lcf2 paramIndexByteString           paramIndexByteString
    paramEqualsByteString                <- getParams lcf2 paramEqualsByteString          paramEqualsByteString
    paramLessThanByteString              <- getParams lcf2 paramLessThanByteString        paramLessThanByteString
    paramLessThanEqualsByteString        <- getParams lcf2 paramLessThanEqualsByteString  paramLessThanEqualsByteString
    -- Cryptography and hashes
    paramSha2_256                        <- getParams lcf1 paramSha2_256                         paramSha2_256
    paramSha3_256                        <- getParams lcf1 paramSha3_256                         paramSha3_256
    paramBlake2b_256                     <- getParams lcf1 paramBlake2b_256                      paramBlake2b_256
    paramVerifyEd25519Signature          <- getParams lcf3 paramVerifyEd25519Signature           paramVerifyEd25519Signature
    paramVerifyEcdsaSecp256k1Signature   <- getParams lcf3 paramVerifyEcdsaSecp256k1Signature    paramVerifyEcdsaSecp256k1Signature
    paramVerifySchnorrSecp256k1Signature <- getParams lcf3 paramVerifySchnorrSecp256k1Signature  paramVerifySchnorrSecp256k1Signature
    -- Strings
    paramAppendString                    <- getParams lcf2 paramAppendString  paramAppendString
    paramEqualsString                    <- getParams lcf2 paramEqualsString  paramEqualsString
    paramEncodeUtf8                      <- getParams lcf1 paramEncodeUtf8    paramEncodeUtf8
    paramDecodeUtf8                      <- getParams lcf1 paramDecodeUtf8    paramDecodeUtf8
    -- Bool
    paramIfThenElse                      <- getParams lcf3 paramIfThenElse     paramIfThenElse
    -- Unit
    paramChooseUnit                      <- getParams lcf2 paramChooseUnit     paramChooseUnit
    -- Tracing
    paramTrace                           <- getParams lcf2 paramTrace          paramTrace
    -- Pairs
    paramFstPair                         <- getParams lcf1 paramFstPair        paramFstPair
    paramSndPair                         <- getParams lcf1 paramSndPair        paramSndPair
    -- Lists
    paramChooseList                      <- getParams lcf3 paramChooseList     paramChooseList
    paramMkCons                          <- getParams lcf2 paramMkCons         paramMkCons
    paramHeadList                        <- getParams lcf1 paramHeadList       paramHeadList
    paramTailList                        <- getParams lcf1 paramTailList       paramTailList
    paramNullList                        <- getParams lcf1 paramNullList       paramNullList
    -- Data
    paramChooseData                      <- getParams lcf6 paramChooseData     paramChooseData
    paramConstrData                      <- getParams lcf2 paramConstrData     paramConstrData
    paramMapData                         <- getParams lcf1 paramMapData        paramMapData
    paramListData                        <- getParams lcf1 paramListData       paramListData
    paramIData                           <- getParams lcf1 paramIData          paramIData
    paramBData                           <- getParams lcf1 paramBData          paramBData
    paramUnConstrData                    <- getParams lcf1 paramUnConstrData   paramUnConstrData
    paramUnMapData                       <- getParams lcf1 paramUnMapData      paramUnMapData
    paramUnListData                      <- getParams lcf1 paramUnListData     paramUnListData
    paramUnIData                         <- getParams lcf1 paramUnIData        paramUnIData
    paramUnBData                         <- getParams lcf1 paramUnBData        paramUnBData
    paramEqualsData                      <- getParams lcf2 paramEqualsData     paramEqualsData
    paramSerialiseData                   <- getParams lcf1 paramSerialiseData  paramSerialiseData
    -- Misc constructors
    paramMkPairData                      <- getParams lcf2 paramMkPairData     paramMkPairData
    paramMkNilData                       <- getParams lcf1 paramMkNilData      paramMkNilData
    paramMkNilPairData                   <- getParams lcf1 paramMkNilPairData  paramMkNilPairData
    -- BLS12-381
    paramBls12_381_G1_add                <- getParams lcf2 paramBls12_381_G1_add          paramBls12_381_G1_add
    paramBls12_381_G1_neg                <- getParams lcf1 paramBls12_381_G1_neg          paramBls12_381_G1_neg
    paramBls12_381_G1_scalarMul          <- getParams lcf2 paramBls12_381_G1_scalarMul    paramBls12_381_G1_scalarMul
    paramBls12_381_G1_equal              <- getParams lcf2 paramBls12_381_G1_equal        paramBls12_381_G1_equal
    paramBls12_381_G1_compress           <- getParams lcf1 paramBls12_381_G1_compress     paramBls12_381_G1_compress
    paramBls12_381_G1_uncompress         <- getParams lcf1 paramBls12_381_G1_uncompress   paramBls12_381_G1_uncompress
    paramBls12_381_G1_hashToGroup        <- getParams lcf2 paramBls12_381_G1_hashToGroup  paramBls12_381_G1_hashToGroup
    paramBls12_381_G2_add                <- getParams lcf2 paramBls12_381_G2_add          paramBls12_381_G2_add
    paramBls12_381_G2_neg                <- getParams lcf1 paramBls12_381_G2_neg          paramBls12_381_G2_neg
    paramBls12_381_G2_scalarMul          <- getParams lcf2 paramBls12_381_G2_scalarMul    paramBls12_381_G2_scalarMul
    paramBls12_381_G2_equal              <- getParams lcf2 paramBls12_381_G2_equal        paramBls12_381_G2_equal
    paramBls12_381_G2_compress           <- getParams lcf1 paramBls12_381_G2_compress     paramBls12_381_G2_compress
    paramBls12_381_G2_uncompress         <- getParams lcf1 paramBls12_381_G2_uncompress   paramBls12_381_G2_uncompress
    paramBls12_381_G2_hashToGroup        <- getParams lcf2 paramBls12_381_G2_hashToGroup  paramBls12_381_G2_hashToGroup
    paramBls12_381_millerLoop            <- getParams lcf2 paramBls12_381_millerLoop      paramBls12_381_millerLoop
    paramBls12_381_mulMlResult           <- getParams lcf2 paramBls12_381_mulMlResult     paramBls12_381_mulMlResult
    paramBls12_381_finalVerify           <- getParams lcf2 paramBls12_381_finalVerify     paramBls12_381_finalVerify
    -- More hashes
    paramKeccak_256                      <- getParams lcf1 paramKeccak_256           paramKeccak_256
    paramBlake2b_224                     <- getParams lcf1 paramBlake2b_224          paramBlake2b_224
    -- Bitwise operations
    paramByteStringToInteger             <- getParams lcf2 paramByteStringToInteger  paramByteStringToInteger
    paramIntegerToByteString             <- getParams lcf3 paramIntegerToByteString  paramIntegerToByteString

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
getCoeff f e = microToPico . fromSomeSEXP  <$> [r| e_hs$coefficients[[f_hs]] |]

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


lcf1 :: MonadR m => SomeSEXP (Region m) -> m ModelOneArgument
lcf1 = loadOneVariableCostingFunction

lcf2 :: MonadR m => SomeSEXP (Region m) -> m ModelTwoArguments
lcf2 = loadTwoVariableCostingFunction

lcf3 :: MonadR m => SomeSEXP (Region m) -> m ModelThreeArguments
lcf3 = loadThreeVariableCostingFunction

lcf6 :: MonadR m => SomeSEXP (Region m) -> m ModelSixArguments
lcf6 = loadSixVariableCostingFunction


boolMemModel :: ModelTwoArguments
boolMemModel = ModelTwoArgumentsConstantCost 1

memoryUsageAsCostingInteger :: ExMemoryUsage a => a -> CostingInteger
memoryUsageAsCostingInteger = coerce . sumCostStream . flattenCostRose . memoryUsage

hashMemModel :: (ByteString -> ByteString) -> ModelOneArgument
hashMemModel f = ModelOneArgumentConstantCost $ memoryUsageAsCostingInteger $ f ""

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

newtype Id a = Id { getId :: a }

builtinMemModels :: BuiltinCostModelBase Id
builtinMemModels = BuiltinCostModelBase
  { paramAddInteger                      = Id $ ModelTwoArgumentsMaxSize $ OneVariableLinearFunction 1 1
  , paramSubtractInteger                 = Id $ ModelTwoArgumentsMaxSize $ OneVariableLinearFunction 1 1
  , paramMultiplyInteger                 = Id $ ModelTwoArgumentsAddedSizes $ OneVariableLinearFunction 0 1
  , paramDivideInteger                   = Id $ ModelTwoArgumentsSubtractedSizes $ ModelSubtractedSizes 0 1 1
  -- ^ Really?  We don't always have size(a/b) = size a - size b
  , paramQuotientInteger                 = Id $ ModelTwoArgumentsSubtractedSizes $ ModelSubtractedSizes 0 1 1
  , paramRemainderInteger                = Id $ ModelTwoArgumentsSubtractedSizes $ ModelSubtractedSizes 0 1 1
  , paramModInteger                      = Id $ ModelTwoArgumentsSubtractedSizes $ ModelSubtractedSizes 0 1 1
  , paramEqualsInteger                   = Id $ boolMemModel
  , paramLessThanInteger                 = Id $ boolMemModel
  , paramLessThanEqualsInteger           = Id $ boolMemModel
  , paramAppendByteString                = Id $ ModelTwoArgumentsAddedSizes $ OneVariableLinearFunction 0 1
  , paramConsByteString                  = Id $ ModelTwoArgumentsAddedSizes $ OneVariableLinearFunction 0 1
  , paramSliceByteString                 = Id $ ModelThreeArgumentsLinearInZ $ OneVariableLinearFunction 4 0
  , paramLengthOfByteString              = Id $ ModelOneArgumentConstantCost 10
  , paramIndexByteString                 = Id $ ModelTwoArgumentsConstantCost 4
  , paramEqualsByteString                = Id $ boolMemModel
  , paramLessThanByteString              = Id $ boolMemModel
  , paramLessThanEqualsByteString        = Id $ boolMemModel
  , paramSha2_256                        = Id $ hashMemModel Hash.sha2_256
  , paramSha3_256                        = Id $ hashMemModel Hash.sha3_256
  , paramBlake2b_256                     = Id $ hashMemModel Hash.blake2b_256
  , paramVerifyEd25519Signature          = Id $ ModelThreeArgumentsConstantCost 10
  , paramVerifyEcdsaSecp256k1Signature   = Id $ ModelThreeArgumentsConstantCost 10
  , paramVerifySchnorrSecp256k1Signature = Id $ ModelThreeArgumentsConstantCost 10
  , paramAppendString                    = Id $ ModelTwoArgumentsAddedSizes $ OneVariableLinearFunction 4 1
  , paramEqualsString                    = Id $ boolMemModel
  , paramEncodeUtf8                      = Id $ ModelOneArgumentLinearCost $ OneVariableLinearFunction 4 2
  , paramDecodeUtf8                      = Id $ ModelOneArgumentLinearCost $ OneVariableLinearFunction 4 2
  , paramIfThenElse                      = Id $ ModelThreeArgumentsConstantCost 1
  , paramChooseUnit                      = Id $ ModelTwoArgumentsConstantCost 4
  , paramTrace                           = Id $ ModelTwoArgumentsConstantCost 32
  , paramFstPair                         = Id $ ModelOneArgumentConstantCost 32
  , paramSndPair                         = Id $ ModelOneArgumentConstantCost 32
  , paramChooseList                      = Id $ ModelThreeArgumentsConstantCost 32
  , paramMkCons                          = Id $ ModelTwoArgumentsConstantCost 32
  , paramHeadList                        = Id $ ModelOneArgumentConstantCost 32
  , paramTailList                        = Id $ ModelOneArgumentConstantCost 32
  , paramNullList                        = Id $ ModelOneArgumentConstantCost 32
  , paramChooseData                      = Id $ ModelSixArgumentsConstantCost 32
  , paramConstrData                      = Id $ ModelTwoArgumentsConstantCost 32
  , paramMapData                         = Id $ ModelOneArgumentConstantCost 32
  , paramListData                        = Id $ ModelOneArgumentConstantCost 32
  , paramIData                           = Id $ ModelOneArgumentConstantCost 32
  , paramBData                           = Id $ ModelOneArgumentConstantCost 32
  , paramUnConstrData                    = Id $ ModelOneArgumentConstantCost 32
  , paramUnMapData                       = Id $ ModelOneArgumentConstantCost 32
  , paramUnListData                      = Id $ ModelOneArgumentConstantCost 32
  , paramUnIData                         = Id $ ModelOneArgumentConstantCost 32
  , paramUnBData                         = Id $ ModelOneArgumentConstantCost 32
  , paramEqualsData                      = Id $ ModelTwoArgumentsConstantCost 1
  , paramMkPairData                      = Id $ ModelTwoArgumentsConstantCost 32
  , paramMkNilData                       = Id $ ModelOneArgumentConstantCost 32
  , paramMkNilPairData                   = Id $ ModelOneArgumentConstantCost 32
  , paramSerialiseData                   = Id $ ModelOneArgumentLinearCost $ OneVariableLinearFunction 0 2
  , paramBls12_381_G1_add                = Id $ ModelTwoArgumentsConstantCost g1MemSize
  , paramBls12_381_G1_neg                = Id $ ModelOneArgumentConstantCost g1MemSize
  , paramBls12_381_G1_scalarMul          = Id $ ModelTwoArgumentsConstantCost g1MemSize
  , paramBls12_381_G1_equal              = Id $ boolMemModel
  , paramBls12_381_G1_compress           = Id $ ModelOneArgumentConstantCost g1CompressedSize
  , paramBls12_381_G1_uncompress         = Id $ ModelOneArgumentConstantCost g1MemSize
  , paramBls12_381_G1_hashToGroup        = Id $ ModelTwoArgumentsConstantCost g1MemSize
  , paramBls12_381_G2_add                = Id $ ModelTwoArgumentsConstantCost g2MemSize
  , paramBls12_381_G2_neg                = Id $ ModelOneArgumentConstantCost g2MemSize
  , paramBls12_381_G2_scalarMul          = Id $ ModelTwoArgumentsConstantCost g2MemSize
  , paramBls12_381_G2_equal              = Id $ boolMemModel
  , paramBls12_381_G2_compress           = Id $ ModelOneArgumentConstantCost g2CompressedSize
  , paramBls12_381_G2_uncompress         = Id $ ModelOneArgumentConstantCost g2MemSize
  , paramBls12_381_G2_hashToGroup        = Id $ ModelTwoArgumentsConstantCost g2MemSize
  , paramBls12_381_millerLoop            = Id $ ModelTwoArgumentsConstantCost mlResultMemSize
  , paramBls12_381_mulMlResult           = Id $ ModelTwoArgumentsConstantCost mlResultMemSize
  , paramBls12_381_finalVerify           = Id $ boolMemModel
  , paramBlake2b_224                     = Id $ hashMemModel Hash.blake2b_224
  , paramKeccak_256                      = Id $ hashMemModel Hash.keccak_256
  , paramIntegerToByteString             = Id $ ModelThreeArgumentsLiteralInYOrLinearInZ $ OneVariableLinearFunction 0 1
  , paramByteStringToInteger             = Id $ ModelTwoArgumentsLinearInY $ OneVariableLinearFunction 0 1
  }

