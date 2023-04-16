-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CreateBuiltinCostModel where

import PlutusCore.Crypto.BLS12_381.G1 qualified as G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as Pairing
import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.CostStream
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Machine.ExMemoryUsage

import Barbies (bmap, bsequence)
import Control.Applicative (Const (Const, getConst))
import Control.Exception (TypeError (TypeError))
import Control.Monad.Catch (throwM)
import Data.ByteString.Hash qualified as PlutusHash
import Data.ByteString.Lazy qualified as BSL (fromStrict)
import Data.Coerce (coerce)
import Data.Csv (FromNamedRecord, FromRecord, HasHeader (HasHeader), decode, parseNamedRecord, (.:))
import Data.Either.Extra (maybeToEither)
import Data.Functor.Compose (Compose (Compose))
import Data.SatInt
import Data.Text (Text)
import Data.Text.Encoding qualified as T (encodeUtf8)
import Data.Vector (Vector, find)
import GHC.Generics (Generic)

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

-- ! Creates the cost model from a CSV benchmarking results file and a file
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
    paramSha2_256                        <- getParams sha2_256                        paramSha2_256
    paramSha3_256                        <- getParams sha3_256                        paramSha3_256
    paramBlake2b_256                     <- getParams blake2b_256                     paramBlake2b_256
    paramVerifyEd25519Signature          <- getParams verifyEd25519Signature          paramVerifyEd25519Signature
    paramVerifyEcdsaSecp256k1Signature   <- getParams verifyEcdsaSecp256k1Signature   paramVerifyEcdsaSecp256k1Signature
    paramVerifySchnorrSecp256k1Signature <- getParams verifySchnorrSecp256k1Signature paramVerifySchnorrSecp256k1Signature
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

    paramBls12_381_G1_add            <- getParams bls12_381_G1_add         paramBls12_381_G1_add
    paramBls12_381_G1_neg            <- getParams bls12_381_G1_neg         paramBls12_381_G1_neg
    paramBls12_381_G1_scalarMul      <- getParams bls12_381_G1_scalarMul   paramBls12_381_G1_scalarMul
    paramBls12_381_G1_equal          <- getParams bls12_381_G1_equal       paramBls12_381_G1_equal
    paramBls12_381_G1_compress       <- getParams bls12_381_G1_compress    paramBls12_381_G1_compress
    paramBls12_381_G1_uncompress     <- getParams bls12_381_G1_uncompress  paramBls12_381_G1_uncompress
    paramBls12_381_G1_hashToGroup    <- getParams bls12_381_G1_hashToGroup paramBls12_381_G1_hashToGroup
    paramBls12_381_G2_add            <- getParams bls12_381_G2_add         paramBls12_381_G2_add
    paramBls12_381_G2_neg            <- getParams bls12_381_G2_neg         paramBls12_381_G2_neg
    paramBls12_381_G2_scalarMul      <- getParams bls12_381_G2_scalarMul   paramBls12_381_G2_scalarMul
    paramBls12_381_G2_equal          <- getParams bls12_381_G2_equal       paramBls12_381_G2_equal
    paramBls12_381_G2_compress       <- getParams bls12_381_G2_compress    paramBls12_381_G2_compress
    paramBls12_381_G2_uncompress     <- getParams bls12_381_G2_uncompress  paramBls12_381_G2_uncompress
    paramBls12_381_G2_hashToGroup    <- getParams bls12_381_G2_hashToGroup paramBls12_381_G2_hashToGroup
    paramBls12_381_millerLoop        <- getParams bls12_381_millerLoop     paramBls12_381_millerLoop
    paramBls12_381_mulMlResult       <- getParams bls12_381_mulMlResult    paramBls12_381_mulMlResult
    paramBls12_381_finalVerify       <- getParams bls12_381_finalVerify    paramBls12_381_finalVerify

    pure $ BuiltinCostModelBase {..}

-- The output of `tidy(model)` on the R side.
-- FIXME: we ignore most of this.  Should we just return the vector of coefficients for the model?
data LinearModelRaw = LinearModelRaw
  { linearModelIndex        :: Integer
  , linearModelRawTerm      :: String
  , linearModelRawEstimate  :: Double
  , linearModelRawStdError  :: Double
  , linearModelRawStatistic :: Double
  , linearModelRawPValue    :: Double
  } deriving stock (Show, Eq, Generic)

-- Reading via CSV because the R side did weird things in JSON
instance FromNamedRecord LinearModelRaw where
  parseNamedRecord v =
      LinearModelRaw
        <$> v .: ""
        <*> v .: "term"
        <*> v .: "estimate"
        <*> v .: "std.error"
        <*> v .: "statistic"
        <*> v .: "p.value"

instance FromRecord LinearModelRaw


findInRaw :: String -> Vector LinearModelRaw -> Either String LinearModelRaw
findInRaw s v = maybeToEither ("Couldn't find the term " <> s <> " in " <> show v) $
  Data.Vector.find (\e -> linearModelRawTerm e == s) v

-- t = ax+c
unsafeReadModelFromR :: MonadR m => String -> (SomeSEXP (Region m)) -> m (CostingInteger, CostingInteger)
unsafeReadModelFromR formula rmodel = do
  j <- [r| write.csv(tidy(rmodel_hs), file=textConnection("out", "w", local=TRUE))
          paste(out, collapse="\n") |]
  let m = do
        model     <- Data.Csv.decode HasHeader $ BSL.fromStrict $ T.encodeUtf8 $ (fromSomeSEXP j :: Text)
        intercept <- linearModelRawEstimate <$> findInRaw "(Intercept)" model
        slope     <- linearModelRawEstimate <$> findInRaw formula model
        pure $ (microToPico intercept, microToPico slope)
  case m of
    Left err -> throwM (TypeError err)
    Right x  -> pure x

-- t = ax+by+c
unsafeReadModelFromR2 :: MonadR m => String -> String -> (SomeSEXP (Region m)) -> m (CostingInteger, CostingInteger, CostingInteger)
unsafeReadModelFromR2 formula1 formula2 rmodel = do
  j <- [r| write.csv(tidy(rmodel_hs), file=textConnection("out", "w", local=TRUE))
          paste(out, collapse="\n") |]
  let m = do
        model     <- Data.Csv.decode HasHeader $ BSL.fromStrict $ T.encodeUtf8 $ (fromSomeSEXP j :: Text)
        intercept <- linearModelRawEstimate <$> findInRaw "(Intercept)" model
        slope1    <- linearModelRawEstimate <$> findInRaw formula1 model
        slope2    <- linearModelRawEstimate <$> findInRaw formula2 model
        pure $ (microToPico intercept, microToPico slope1, microToPico slope2)
  case m of
    Left err -> throwM (TypeError err)
    Right x  -> pure x

readModelAddedSizes :: MonadR m => (SomeSEXP (Region m)) -> m ModelAddedSizes
readModelAddedSizes model = (pure . uncurry ModelAddedSizes) =<< unsafeReadModelFromR "I(x_mem + y_mem)" model

readModelMinSize :: MonadR m => (SomeSEXP (Region m)) -> m ModelMinSize
readModelMinSize model = (pure . uncurry ModelMinSize) =<< unsafeReadModelFromR "pmin(x_mem, y_mem)" model

readModelMaxSize :: MonadR m => (SomeSEXP (Region m)) -> m ModelMaxSize
readModelMaxSize model = (pure . uncurry ModelMaxSize) =<< unsafeReadModelFromR "pmax(x_mem, y_mem)" model

uncurry3 :: (a -> b -> c -> d) -> ((a, b, c) -> d)
uncurry3 f ~(a,b,c) = f a b c


readModelMultipliedSizes :: MonadR m => (SomeSEXP (Region m)) -> m ModelMultipliedSizes
readModelMultipliedSizes model = (pure . uncurry ModelMultipliedSizes) =<< unsafeReadModelFromR "I(x_mem * y_mem)" model

readModelConstantCost :: MonadR m => (SomeSEXP (Region m)) -> m CostingInteger
readModelConstantCost model = (\(i, _i) -> pure  i) =<< unsafeReadModelFromR "(Intercept)" model

readModelLinearInX :: MonadR m => (SomeSEXP (Region m)) -> m ModelLinearSize
readModelLinearInX model = (\(intercept, slope) -> pure $ ModelLinearSize intercept slope) =<< unsafeReadModelFromR "x_mem" model

readModelLinearInY :: MonadR m => (SomeSEXP (Region m)) -> m ModelLinearSize
readModelLinearInY model = (\(intercept, slope) -> pure $ ModelLinearSize intercept slope) =<< unsafeReadModelFromR "y_mem" model

-- For models which are linear on the diagonal and constant elsewhere we currently
-- only benchmark and model the linear part, so here we read in the model from R
-- and supply the constant as a parameter
readModelLinearOnDiagonal :: MonadR m => (SomeSEXP (Region m)) -> CostingInteger -> m ModelConstantOrLinear
readModelLinearOnDiagonal model c = do
  (intercept, slope) <- unsafeReadModelFromR "x_mem" model
  pure $ ModelConstantOrLinear c intercept slope

boolMemModel :: ModelTwoArguments
boolMemModel = ModelTwoArgumentsConstantCost 1

memoryUsageAsCostingInteger :: ExMemoryUsage a => a -> CostingInteger
memoryUsageAsCostingInteger = coerce . sumCostStream . flattenCostRose . memoryUsage


---------------- Integers ----------------

addInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
addInteger cpuModelR = do
  cpuModel <- ModelTwoArgumentsMaxSize <$> readModelMaxSize cpuModelR
  -- The worst case is adding e.g. `maxBound :: Int` + `maxBound :: Int`, which increases the memory usage by one.
  -- (max x y) + 1
  let memModel = ModelTwoArgumentsMaxSize $ ModelMaxSize 1 1
  pure $ CostingFun cpuModel memModel

subtractInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
subtractInteger cpuModelR = do
  cpuModel <- ModelTwoArgumentsMaxSize <$> readModelMaxSize cpuModelR
  -- The worst case is subtracting e.g. `minBound :: Int` - `maxBound :: Int`, which increases the memory usage by one.
  -- (max x y) + 1
  let memModel = ModelTwoArgumentsMaxSize $ ModelMaxSize 1 1
  pure $ CostingFun (cpuModel) memModel

multiplyInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
multiplyInteger cpuModelR = do
  cpuModel <- ModelTwoArgumentsAddedSizes <$> readModelAddedSizes cpuModelR
  -- GMP requires multiplication (mpn_mul) to have x + y space.
  -- x + y
  let memModel = ModelTwoArgumentsAddedSizes $ ModelAddedSizes 0 1
  pure $ CostingFun (cpuModel) memModel

divideInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
divideInteger cpuModelR = do
  cpuModelBelowDiag <- readModelMultipliedSizes cpuModelR
  let cpuModel = ModelTwoArgumentsConstAboveDiagonal
                 (ModelConstantOrTwoArguments 196500 $
                  ModelTwoArgumentsMultipliedSizes cpuModelBelowDiag
                  -- ### FIXME: the constant above is currently obtained manually from R; automate this
                 )
  -- GMP requires division (mpn_divrem) to have x - y space.
  -- x - y
  let memModel = ModelTwoArgumentsSubtractedSizes $ ModelSubtractedSizes 0 1 1
  pure $ CostingFun cpuModel memModel

quotientInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
quotientInteger cpuModelR = do
  cpuModelBelowDiag <- readModelMultipliedSizes cpuModelR
  let cpuModel = ModelTwoArgumentsConstAboveDiagonal
                 (ModelConstantOrTwoArguments 196500 $
                  ModelTwoArgumentsMultipliedSizes cpuModelBelowDiag
                  -- ### FIXME: the constant above is currently obtained manually from R; automate this
                 )
  -- GMP requires division (mpn_divrem) to have x - y space.
  -- x - y
  let memModel = ModelTwoArgumentsSubtractedSizes $ ModelSubtractedSizes 0 1 1
  pure $ CostingFun cpuModel memModel

remainderInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
remainderInteger = quotientInteger

modInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
modInteger = divideInteger

-- FIXME: should probably be piecewise (harmless, but may overprice some comparisons a bit)
equalsInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
equalsInteger cpuModelR = do
  cpuModel <- ModelTwoArgumentsMinSize <$> readModelMinSize cpuModelR
  pure $ CostingFun cpuModel boolMemModel

lessThanInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
lessThanInteger cpuModelR = do
  cpuModel <- ModelTwoArgumentsMinSize <$> readModelMinSize cpuModelR
  pure $ CostingFun (cpuModel) boolMemModel

lessThanEqualsInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
lessThanEqualsInteger cpuModelR = do
  cpuModel <- ModelTwoArgumentsMinSize <$> readModelMinSize cpuModelR
  pure $ CostingFun cpuModel boolMemModel


---------------- Bytestrings ----------------

appendByteString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
appendByteString cpuModelR = do
  cpuModel <- ModelTwoArgumentsAddedSizes <$> readModelAddedSizes cpuModelR
  let memModel = ModelTwoArgumentsAddedSizes $ ModelAddedSizes 0 1
  pure $ CostingFun cpuModel memModel

consByteString ::  MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
consByteString cpuModelR = do
  m <- readModelLinearInY cpuModelR
  let cpuModel = ModelTwoArgumentsLinearInY m
      memModel = ModelTwoArgumentsAddedSizes $ ModelAddedSizes 0 1
  pure $ CostingFun cpuModel memModel


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
sliceByteString ::  MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
sliceByteString cpuModelR = do
  c <- readModelConstantCost cpuModelR
  let cpuModel = ModelThreeArgumentsLinearInZ $ ModelLinearSize c 0
  let memModel = ModelThreeArgumentsLinearInZ $ ModelLinearSize 4 0
  pure $ CostingFun cpuModel memModel

lengthOfByteString ::  MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
lengthOfByteString cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 10
  pure $ CostingFun cpuModel memModel

indexByteString ::  MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
indexByteString cpuModelR = do
  cpuModel <- ModelTwoArgumentsConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelTwoArgumentsConstantCost 4
  pure $ CostingFun cpuModel memModel

equalsByteString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
equalsByteString cpuModelR = do
  cpuModel <- ModelTwoArgumentsLinearOnDiagonal <$> readModelLinearOnDiagonal cpuModelR 245000
                  -- ### FIXME: the constant above is currently obtained manually from R; automate this
  pure $ CostingFun cpuModel boolMemModel

lessThanByteString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
lessThanByteString cpuModelR = do
  cpuModel <- ModelTwoArgumentsMinSize <$> readModelMinSize cpuModelR
  pure $ CostingFun (cpuModel) boolMemModel

lessThanEqualsByteString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
lessThanEqualsByteString = lessThanByteString


---------------- Cryptography and hashes ----------------

sha2_256 :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
sha2_256 cpuModelR = do
  cpuModel <- ModelOneArgumentLinearCost <$> readModelLinearInX cpuModelR
  let memModel = ModelOneArgumentConstantCost (memoryUsageAsCostingInteger $ PlutusHash.sha2_256 "")
  pure $ CostingFun cpuModel memModel

sha3_256 :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
sha3_256 cpuModelR = do
  cpuModel <- ModelOneArgumentLinearCost <$> readModelLinearInX cpuModelR
  let memModel = ModelOneArgumentConstantCost (memoryUsageAsCostingInteger $ PlutusHash.sha3_256 "")
  pure $ CostingFun cpuModel memModel

blake2b_256 :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
blake2b_256 cpuModelR = do
  cpuModel <- ModelOneArgumentLinearCost <$> readModelLinearInX cpuModelR
  let memModel = ModelOneArgumentConstantCost (memoryUsageAsCostingInteger $ PlutusHash.blake2b_256 "")
  pure $ CostingFun cpuModel memModel

-- NB: the R model is based purely on the size of the second argument (since the
-- first and third are constant size), so we have to rearrange things a bit to
-- get it to work with a three-argument costing function.
verifyEd25519Signature :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
verifyEd25519Signature cpuModelR = do
  cpuModel <- ModelThreeArgumentsLinearInZ <$> readModelLinearInY cpuModelR
  let memModel =  ModelThreeArgumentsConstantCost 10
  pure $ CostingFun cpuModel memModel
  {- The CPU model is wrong here, but not in the way that it may appear to be.
     We're reading a model for Y but treating it as a function of Z. This is
     because the model was accidentally based on the size of the third argument,
     which is a 64-byte signature.  However, we should really be modelling it as
     a function of Y, since that's the 'message' parameter of the
     verifyEd25519Signature function.  So above it should say

        ModelThreeArgumentsLinearInY <$> readModelLinearInY cpuModelR.

     To recapitulate, R is supplying us with a reasonable model for execution
     time in terms of message size, but we're feeding that model constant inputs
     (the size of the signature, 64 bytes/8 words) instead of the size of the
     signature that we're verifying.  Luckily we can get away with this.  The
     time taken to run verifyEd25519Signature in fact appears to be effectively
     constant, even for very large messages, possibly because the underlying C
     code is very fast.  The Z-based cost function returns a constant cost since
     the size of the third argument is constant; we should be using a Y-based
     function instead, but that would give similar results and we're not
     undercharging siginficantly.  To fix this we need to change the shape of
     the model from "linear_in_z" to "linear_in_y", but that's something we need
     to be careful about: see SCP-3038.
   -}

verifyEcdsaSecp256k1Signature :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
verifyEcdsaSecp256k1Signature cpuModelR = do
  cpuModel <- ModelThreeArgumentsConstantCost <$> readModelConstantCost cpuModelR
  let memModel =  ModelThreeArgumentsConstantCost 10
  pure $ CostingFun cpuModel memModel

verifySchnorrSecp256k1Signature :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
verifySchnorrSecp256k1Signature cpuModelR = do
  cpuModel <- ModelThreeArgumentsLinearInY <$> readModelLinearInY cpuModelR
  let memModel =  ModelThreeArgumentsConstantCost 10
  pure $ CostingFun cpuModel memModel

---------------- Strings ----------------

appendString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
appendString cpuModelR = do
  cpuModel <- ModelTwoArgumentsAddedSizes <$> readModelAddedSizes cpuModelR
  let memModel = ModelTwoArgumentsAddedSizes $ ModelAddedSizes 4 1
  pure $ CostingFun cpuModel memModel

equalsString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
equalsString cpuModelR = do
  cpuModel <- ModelTwoArgumentsLinearOnDiagonal <$> readModelLinearOnDiagonal cpuModelR 187000
  -- ### FIXME: the constant above is currently obtained manually from R; automate this
  let memModel = boolMemModel
  pure $ CostingFun cpuModel memModel

encodeUtf8 :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
encodeUtf8 cpuModelR = do
  cpuModel <- ModelOneArgumentLinearCost <$> readModelLinearInX cpuModelR
  let memModel = ModelOneArgumentLinearCost $ ModelLinearSize 4 2
                 -- In the worst case two UTF-16 bytes encode to three UTF-8
                 -- bytes, so two output words per input word should cover that.
  pure $ CostingFun cpuModel memModel

decodeUtf8 :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
decodeUtf8 cpuModelR = do
  cpuModel <- ModelOneArgumentLinearCost <$> readModelLinearInX cpuModelR
  let memModel = ModelOneArgumentLinearCost $ ModelLinearSize 4 2
                 -- In the worst case one UTF-8 byte decodes to two UTF-16 bytes
  pure $ CostingFun cpuModel memModel


---------------- Bool ----------------
ifThenElse :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
ifThenElse cpuModelR = do
  cpuModel <- ModelThreeArgumentsConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelThreeArgumentsConstantCost 1
  pure $ CostingFun cpuModel memModel

---------------- Unit ----------------

chooseUnit :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
chooseUnit cpuModelR = do
    cpuModel <- ModelTwoArgumentsConstantCost <$> readModelConstantCost cpuModelR
    let memModel = ModelTwoArgumentsConstantCost 4
    pure $ CostingFun cpuModel memModel
-- \() a -> a

---------------- Tracing ----------------

trace :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
trace cpuModelR = do
  cpuModel <- ModelTwoArgumentsConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelTwoArgumentsConstantCost 32
  pure $ CostingFun  cpuModel memModel

---------------- Pairs ----------------

fstPair :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
fstPair cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
-- (x,_) -> x; but with lots of Some's etc.

sndPair :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
sndPair cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
-- (_,y) -> y; but with lots of Some's etc.


---------------- Lists ----------------

chooseList :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
chooseList cpuModelR = do
  cpuModel <- ModelThreeArgumentsConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelThreeArgumentsConstantCost 32
  pure $ CostingFun cpuModel memModel
-- xs a b -> a if xs == [], b otherwise

mkCons :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
mkCons cpuModelR = do
  cpuModel <- ModelTwoArgumentsConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelTwoArgumentsConstantCost 32
  pure $ CostingFun cpuModel memModel
-- x xs -> x:xs, but with a dynamic type check

headList :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
headList cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
-- x:_ -> x, [] -> failure.  Successful case has fromValueOf etc.

tailList :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
tailList cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
-- Like headList

nullList :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
nullList cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
-- x::[a] -> Bool

---------------- Data ----------------

chooseData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelSixArguments)
chooseData cpuModelR = do
  cpuModel <- ModelSixArgumentsConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelSixArgumentsConstantCost 32
  pure $ CostingFun cpuModel memModel
-- chooseData d p q r s t u  returns one of the last six elements according to what d is.

constrData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
constrData cpuModelR = do
  cpuModel <- ModelTwoArgumentsConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelTwoArgumentsConstantCost 32
  pure $ CostingFun cpuModel memModel
-- Just applying Constr

mapData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
mapData cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
-- Just applying Map

listData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
listData cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
-- Just applying List

iData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
iData cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
-- Just applying I

bData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
bData cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
-- Just applying B

unConstrData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
unConstrData cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
-- Constr i ds -> (i,ds);  _ -> fail

unMapData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
unMapData cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
-- Map es -> es;  _ -> fail

unListData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
unListData cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
-- List ds -> ds;  _ -> fail

unIData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
unIData cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
-- I i -> i;  _ -> fail

unBData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
unBData cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
-- B b -> b;  _ -> fail

equalsData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
equalsData cpuModelR = do
  cpuModel <- ModelTwoArgumentsMinSize <$> readModelMinSize cpuModelR
  let memModel = ModelTwoArgumentsConstantCost 1
  pure $ CostingFun cpuModel memModel
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

serialiseData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
serialiseData cpuModelR = do
  cpuModel <- ModelOneArgumentLinearCost <$> readModelLinearInX cpuModelR
  let memModel = ModelOneArgumentLinearCost $ ModelLinearSize 0 2
  pure $ CostingFun cpuModel memModel

---------------- Misc constructors ----------------

mkPairData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
mkPairData cpuModelR = do
  cpuModel <- ModelTwoArgumentsConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelTwoArgumentsConstantCost 32
  pure $ CostingFun cpuModel memModel
-- a b -> (a,b)

mkNilData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
mkNilData cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
-- () -> [] :: [Data]

mkNilPairData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
mkNilPairData cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost 32
  pure $ CostingFun cpuModel memModel
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

-- Compressed serialised G1 points take up 48 bytes (6 words)
g1CompressedSize :: CostingInteger
g1CompressedSize = toMemSize G1.compressedSizeBytes

-- In-memory G2 points take up 288 bytes (36 words)
g2MemSize :: CostingInteger
g2MemSize = toMemSize G2.memSizeBytes

-- Compressed serialised G2 points take up 96 bytes (12 words)
g2CompressedSize :: CostingInteger
g2CompressedSize = toMemSize G2.compressedSizeBytes

-- In-memory G2 points take up 576 bytes (72 words)
mlResultMemSize :: CostingInteger
mlResultMemSize = toMemSize Pairing.mlResultMemSizeBytes

bls12_381_G1_add :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
bls12_381_G1_add cpuModelR = do
  cpuModel <- ModelTwoArgumentsConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelTwoArgumentsConstantCost g1MemSize
  pure $ CostingFun cpuModel memModel

bls12_381_G1_neg :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
bls12_381_G1_neg cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost g1MemSize
  pure $ CostingFun cpuModel memModel

bls12_381_G1_scalarMul ::  MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
bls12_381_G1_scalarMul cpuModelR = do
  cpuModel <- ModelTwoArgumentsLinearInX <$> readModelLinearInX cpuModelR
  let memModel = ModelTwoArgumentsConstantCost g1MemSize
  pure $ CostingFun cpuModel memModel

bls12_381_G1_equal :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
bls12_381_G1_equal cpuModelR = do
    cpuModel <- ModelTwoArgumentsConstantCost <$> readModelConstantCost cpuModelR
    let memModel = boolMemModel
    pure $ CostingFun cpuModel memModel

bls12_381_G1_hashToGroup :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
bls12_381_G1_hashToGroup cpuModelR = do
    cpuModel <- ModelOneArgumentLinearCost <$> readModelLinearInX cpuModelR
    let memModel = ModelOneArgumentConstantCost g1MemSize
    pure $ CostingFun cpuModel memModel

bls12_381_G1_compress :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
bls12_381_G1_compress cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost g1CompressedSize
  pure $ CostingFun cpuModel memModel

bls12_381_G1_uncompress :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
bls12_381_G1_uncompress cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost g1MemSize
  pure $ CostingFun cpuModel memModel

bls12_381_G2_add :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
bls12_381_G2_add cpuModelR = do
  cpuModel <- ModelTwoArgumentsConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelTwoArgumentsConstantCost g2MemSize
  pure $ CostingFun cpuModel memModel

bls12_381_G2_neg :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
bls12_381_G2_neg cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost g2MemSize
  pure $ CostingFun cpuModel memModel

bls12_381_G2_scalarMul ::  MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
bls12_381_G2_scalarMul cpuModelR = do
  cpuModel <- ModelTwoArgumentsLinearInX <$> readModelLinearInX cpuModelR
  let memModel = ModelTwoArgumentsConstantCost g2MemSize
  pure $ CostingFun cpuModel memModel

bls12_381_G2_equal :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
bls12_381_G2_equal cpuModelR = do
    cpuModel <- ModelTwoArgumentsConstantCost <$> readModelConstantCost cpuModelR
    let memModel = boolMemModel
    pure $ CostingFun cpuModel memModel

bls12_381_G2_hashToGroup :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
bls12_381_G2_hashToGroup cpuModelR = do
    cpuModel <- ModelOneArgumentLinearCost <$> readModelLinearInX cpuModelR
    let memModel = ModelOneArgumentConstantCost g2MemSize
    pure $ CostingFun cpuModel memModel

bls12_381_G2_compress :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
bls12_381_G2_compress cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost g2CompressedSize
  pure $ CostingFun cpuModel memModel

bls12_381_G2_uncompress :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
bls12_381_G2_uncompress cpuModelR = do
  cpuModel <- ModelOneArgumentConstantCost <$> readModelConstantCost cpuModelR
  let memModel = ModelOneArgumentConstantCost g2MemSize
  pure $ CostingFun cpuModel memModel

bls12_381_millerLoop :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
bls12_381_millerLoop cpuModelR = do
    cpuModel <- ModelTwoArgumentsConstantCost <$> readModelConstantCost cpuModelR
    let memModel = ModelTwoArgumentsConstantCost mlResultMemSize
    pure $ CostingFun cpuModel memModel

bls12_381_mulMlResult :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
bls12_381_mulMlResult cpuModelR = do
    cpuModel <- ModelTwoArgumentsConstantCost <$> readModelConstantCost cpuModelR
    let memModel = ModelTwoArgumentsConstantCost mlResultMemSize
    pure $ CostingFun cpuModel memModel

bls12_381_finalVerify :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
bls12_381_finalVerify cpuModelR= do
    cpuModel <- ModelTwoArgumentsConstantCost <$> readModelConstantCost cpuModelR
    let memModel = boolMemModel
    pure $ CostingFun cpuModel memModel


