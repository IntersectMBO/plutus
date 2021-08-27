{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CostModelCreation where

import           PlutusCore.Evaluation.Machine.BuiltinCostModel
import           PlutusCore.Evaluation.Machine.ExMemory

import           Barbies
import           Control.Applicative
import           Control.Exception                              (TypeError (..))
import           Control.Monad.Catch
import qualified Data.ByteString.Hash                           as PlutusHash
import qualified Data.ByteString.Lazy                           as BSL
import           Data.Coerce
import           Data.Csv
import           Data.Either.Extra
import           Data.Functor.Compose
import           Data.Text                                      as T
import qualified Data.Text.Encoding                             as T
import           Data.Vector
import           GHC.Generics

import           Foreign.R
import           H.Prelude                                      (MonadR, Region, r)
import           Language.R

-- | Convert milliseconds represented as a float to picoseconds represented as a
-- CostingInteger.  We round up to be sure we don't underestimate anything.
msToPs :: Double -> CostingInteger
msToPs = ceiling . (1e6 *)

{- See Note [Creation of the Cost Model]
-}

-- TODO some generics magic
-- Mentioned in CostModel.md. Change here, change there.
-- The names of the models in R
builtinCostModelNames :: BuiltinCostModelBase (Const Text)
builtinCostModelNames = BuiltinCostModelBase
  { paramAddInteger               = "addIntegerModel"
  , paramSubtractInteger          = "subtractIntegerModel"
  , paramMultiplyInteger          = "multiplyIntegerModel"
  , paramDivideInteger            = "divideIntegerModel"
  , paramQuotientInteger          = "quotientIntegerModel"
  , paramRemainderInteger         = "remainderIntegerModel"
  , paramModInteger               = "modIntegerModel"
  , paramEqualsInteger            = "equalsIntegerModel"
  , paramLessThanInteger          = "lessThanIntegerModel"
  , paramLessThanEqualsInteger    = "lessThanEqualsIntegerModel"
  , paramAppendByteString         =  "appendByteStringModel"
  , paramConsByteString           =  "consByteStringModel"
  , paramSliceByteString          =  "sliceByteStringModel"
  , paramLengthOfByteString       =  "lengthOfByteStringModel"
  , paramIndexByteString          =  "indexByteStringModel"
  , paramEqualsByteString         =  "equalsByteStringModel"
  , paramLessThanByteString       =  "lessThanByteStringModel"
  , paramLessThanEqualsByteString =  "lessThanEqualsByteStringModel"
  , paramSha2_256                 =  "sha2_256Model"
  , paramSha3_256                 =  "sha3_256Model"
  , paramBlake2b                  =  "blake2bModel"
  , paramVerifySignature          =  "verifySignatureModel"
  , paramAppendString             =  "appendStringModel"
  , paramEqualsString             =  "equalsStringModel"
  , paramEncodeUtf8               =  "encodeUtf8Model"
  , paramDecodeUtf8               =  "decodeUtf8Model"
  , paramIfThenElse               =  "ifThenElseModel"
  , paramChooseUnit               =  "chooseUnitModel"
  , paramTrace                    =  "traceModel"
  , paramFstPair                  =  "fstPairModel"
  , paramSndPair                  =  "sndPairModel"
  , paramChooseList               =  "chooseListModel"
  , paramMkCons                   =  "mkConsModel"
  , paramHeadList                 =  "headListModel"
  , paramTailList                 =  "tailListModel"
  , paramNullList                 =  "nullListModel"
  , paramChooseData               =  "chooseDataModel"
  , paramConstrData               =  "constrDataModel"
  , paramMapData                  =  "mapDataModel"
  , paramListData                 =  "listDataModel"
  , paramIData                    =  "iDataModel"
  , paramBData                    =  "bDataModel"
  , paramUnConstrData             =  "unConstrDataModel"
  , paramUnMapData                =  "unMapDataModel"
  , paramUnListData               =  "unListDataModel"
  , paramUnIData                  =  "unIDataModel"
  , paramUnBData                  =  "unBDataModel"
  , paramEqualsData               =  "equalsDataModel"
  , paramMkPairData               =  "mkPairDataModel"
  , paramMkNilData                =  "mkNilDataModel"
  , paramMkNilPairData            =  "mkNilPairDataModel"
  }

-- Loads the models from R
costModelsR :: MonadR m => m (BuiltinCostModelBase (Const (SomeSEXP (Region m))))
costModelsR = do
  list <- [r|
    source("cost-model/data/models.R")
    modelFun("cost-model/data/benching.csv")
  |]
  -- Unfortunately we can't use the paths defined in DataFilePaths inside [r|...].
  -- The above code may not work on Windows because of that, but we only ever
  -- want to run this on a Linux reference machine anyway.
  bsequence $ bmap (\name -> let n = getConst name in Compose $ fmap Const $ [r| list_hs[[n_hs]] |]) builtinCostModelNames
  -- TODO ^ use btraverse instead

-- Creates the cost model from the csv benchmarking files
createBuiltinCostModel :: IO BuiltinCostModel
createBuiltinCostModel =
  withEmbeddedR defaultConfig $ runRegion $ do
    models <- costModelsR
    -- TODO: refactor with barbies
    let getParams x y = x (getConst $ y models)

    -- Integers
    paramAddInteger               <- getParams addInteger                paramAddInteger
    paramSubtractInteger          <- getParams subtractInteger           paramSubtractInteger
    paramMultiplyInteger          <- getParams multiplyInteger           paramMultiplyInteger
    paramDivideInteger            <- getParams divideInteger             paramDivideInteger
    paramQuotientInteger          <- getParams quotientInteger           paramQuotientInteger
    paramRemainderInteger         <- getParams remainderInteger          paramRemainderInteger
    paramModInteger               <- getParams modInteger                paramModInteger
    paramEqualsInteger            <- getParams equalsInteger             paramEqualsInteger
    paramLessThanInteger          <- getParams lessThanInteger           paramLessThanInteger
    paramLessThanEqualsInteger    <- getParams lessThanEqualsInteger     paramLessThanEqualsInteger
    -- Bytestrings
    paramAppendByteString         <- getParams appendByteString          paramAppendByteString
    paramConsByteString           <- getParams consByteString            paramConsByteString
    paramSliceByteString          <- getParams sliceByteString           paramSliceByteString
    paramLengthOfByteString       <- getParams lengthOfByteString        paramLengthOfByteString
    paramIndexByteString          <- getParams indexByteString           paramIndexByteString
    paramEqualsByteString         <- getParams equalsByteString          paramEqualsByteString
    paramLessThanByteString       <- getParams lessThanByteString        paramLessThanByteString
    paramLessThanEqualsByteString <- getParams lessThanEqualsByteString  paramLessThanEqualsByteString
    -- Cryptography and hashes
    paramSha2_256                 <- getParams sha2_256         paramSha2_256
    paramSha3_256                 <- getParams sha3_256         paramSha3_256
    paramBlake2b                  <- getParams blake2b          paramBlake2b
    paramVerifySignature          <- getParams verifySignature  paramVerifySignature
    -- Strings
    paramAppendString             <- getParams appendString  paramAppendString
    paramEqualsString             <- getParams equalsString  paramEqualsString
    paramEncodeUtf8               <- getParams encodeUtf8    paramEncodeUtf8
    paramDecodeUtf8               <- getParams decodeUtf8    paramDecodeUtf8

    -- Bool
    paramIfThenElse               <- getParams ifThenElse  paramIfThenElse
    -- Unit
    paramChooseUnit               <- getParams chooseUnit  paramChooseUnit
    -- Tracing
    paramTrace                    <- getParams trace       paramTrace
    -- Pairs
    paramFstPair                  <- getParams fstPair     paramFstPair
    paramSndPair                  <- getParams sndPair     paramSndPair
    -- Lists
    paramChooseList               <- getParams chooseList  paramChooseList
    paramMkCons                   <- getParams mkCons      paramMkCons
    paramHeadList                 <- getParams headList    paramHeadList
    paramTailList                 <- getParams tailList    paramTailList
    paramNullList                 <- getParams nullList    paramNullList
    -- Data
    paramChooseData               <- getParams chooseData     paramChooseData
    paramConstrData               <- getParams constrData     paramConstrData
    paramMapData                  <- getParams mapData        paramMapData
    paramListData                 <- getParams listData       paramListData
    paramIData                    <- getParams iData          paramIData
    paramBData                    <- getParams bData          paramBData
    paramUnConstrData             <- getParams unConstrData   paramUnConstrData
    paramUnMapData                <- getParams unMapData      paramUnMapData
    paramUnListData               <- getParams unListData     paramUnListData
    paramUnIData                  <- getParams unIData        paramUnIData
    paramUnBData                  <- getParams unBData        paramUnBData
    paramEqualsData               <- getParams equalsData     paramEqualsData
    -- Misc constructors
    paramMkPairData               <- getParams mkPairData     paramMkPairData
    paramMkNilData                <- getParams mkNilData      paramMkNilData
    paramMkNilPairData            <- getParams mkNilPairData  paramMkNilPairData

    pure $ BuiltinCostModelBase {..}

-- The output of `tidy(model)` on the R side.
data LinearModelRaw = LinearModelRaw
  { linearModelIndex        :: Integer
  , linearModelRawTerm      :: String
  , linearModelRawEstimate  :: Double
  , linearModelRawStdError  :: Double
  , linearModelRawStatistic :: Double
  , linearModelRawPValue    :: Double
  } deriving (Show, Eq, Generic)

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
        pure $ (msToPs intercept, msToPs slope)
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
        pure $ (msToPs intercept, msToPs slope1, msToPs slope2)
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

readModelLinear :: MonadR m => (SomeSEXP (Region m)) -> m ModelLinearSize
readModelLinear model = (\(intercept, slope) -> pure $ ModelLinearSize intercept slope) =<< unsafeReadModelFromR "x_mem" model

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
memoryUsageAsCostingInteger x = coerce $ memoryUsage x


---------------- Integers ----------------

addInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
addInteger cpuModelR = do
  cpuModel <- readModelMaxSize cpuModelR
  -- The worst case is adding e.g. `maxBound :: Int` + `maxBound :: Int`, which increases the memory usage by one.
  -- (max x y) + 1
  let memModel = ModelTwoArgumentsMaxSize $ ModelMaxSize 1 1
  pure $ CostingFun (ModelTwoArgumentsMaxSize cpuModel) memModel

subtractInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
subtractInteger cpuModelR = do
  cpuModel <- readModelMaxSize cpuModelR
  -- The worst case is subtracting e.g. `minBound :: Int` - `maxBound :: Int`, which increases the memory usage by one.
  -- (max x y) + 1
  let memModel = ModelTwoArgumentsMaxSize $ ModelMaxSize 1 1
  pure $ CostingFun (ModelTwoArgumentsMaxSize cpuModel) memModel

multiplyInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
multiplyInteger cpuModelR = do
  cpuModel <- readModelAddedSizes cpuModelR
  -- GMP requires multiplication (mpn_mul) to have x + y space.
  -- x + y
  let memModel = ModelTwoArgumentsAddedSizes $ ModelAddedSizes 0 1
  pure $ CostingFun (ModelTwoArgumentsAddedSizes cpuModel) memModel

divideInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
divideInteger cpuModelR = do
  cpuModelBelowDiag <- readModelMultipliedSizes cpuModelR
  let cpuModel = ModelTwoArgumentsConstAboveDiagonal
                 (ModelConstantOrTwoArguments 148000 $  -- ### Get this number from R
                  ModelTwoArgumentsMultipliedSizes cpuModelBelowDiag
                 )
  -- GMP requires division (mpn_divrem) to have x - y space.
  -- x - y
  let memModel = ModelTwoArgumentsSubtractedSizes $ ModelSubtractedSizes 0 1 1
  pure $ CostingFun cpuModel memModel

quotientInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
quotientInteger cpuModelR = do
  cpuModelBelowDiag <- readModelMultipliedSizes cpuModelR
  let cpuModel = ModelTwoArgumentsConstAboveDiagonal
                 (ModelConstantOrTwoArguments 148000 $ -- ### Get this number from R
                  ModelTwoArgumentsMultipliedSizes cpuModelBelowDiag
                 )
  -- GMP requires division (mpn_divrem) to have x - y space.
  -- x - y
  let memModel = ModelTwoArgumentsSubtractedSizes $ ModelSubtractedSizes 0 1 1
  pure $ CostingFun cpuModel memModel

remainderInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
remainderInteger = quotientInteger

modInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
modInteger = divideInteger

equalsInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
equalsInteger cpuModelR = do
  cpuModel <- readModelMinSize cpuModelR
  pure $ CostingFun (ModelTwoArgumentsMinSize cpuModel) boolMemModel

lessThanInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
lessThanInteger cpuModelR = do
  cpuModel <- readModelMinSize cpuModelR
  pure $ CostingFun (ModelTwoArgumentsMinSize cpuModel) boolMemModel

lessThanEqualsInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
lessThanEqualsInteger cpuModelR = do
  cpuModel <- readModelMinSize cpuModelR
  pure $ CostingFun (ModelTwoArgumentsMinSize cpuModel) boolMemModel


---------------- Bytestrings ----------------

appendByteString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
appendByteString cpuModelR = do
  cpuModel <- readModelAddedSizes cpuModelR
  -- The buffer gets reallocated
  let memModel = ModelTwoArgumentsAddedSizes $ ModelAddedSizes 0 1
  pure $ CostingFun (ModelTwoArgumentsAddedSizes cpuModel) memModel


-- The things marked with ### comments below are plausible guesses at the form
-- of the model to get it fixed for the HF.  Later we'll have to add benchmarks
-- to get data and R code to fit models for all of them.

-- ### TODO: get model from R ###
consByteString ::  MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
consByteString _ = do
      let cpuModel = ModelTwoArgumentsLinearInY $ ModelLinearSize 150000 1000 -- ### Get this from R
      let memModel = ModelTwoArgumentsAddedSizes $ ModelAddedSizes 0 1
      pure $ CostingFun cpuModel memModel


{- | Return a substring of a bytestring with a specified start point and length.
   Plutus Core bytestrings are implemented using Data.ByteString, which
   represents a (strict) bytestring as a C array of bytes together with a
   pointer into that and a length.  The sliceBytestring function is implemented
   using 'take' and 'drop', and these work by modifying the pointer and length;
   no bytes are copied so sliceByteString requires constant time and a constant
   memory overhead.  Nevertheless we use linear costing functions here to leave
   some room for future flexibility.
-}
sliceByteString ::  MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
sliceByteString _ = do
  let cpuModel = ModelThreeArgumentsLinearInZ $ ModelLinearSize 150000 0
  let memModel = ModelThreeArgumentsLinearInZ $ ModelLinearSize 0 20
  pure $ CostingFun cpuModel memModel


-- ### TODO: get model from R ###
lengthOfByteString ::  MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
lengthOfByteString _ = do
      let cpuModel = ModelOneArgumentConstantCost 150000
      let memModel = ModelOneArgumentConstantCost 10
      pure $ CostingFun cpuModel memModel

indexByteString ::  MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
indexByteString _ = do
      let cpuModel = ModelTwoArgumentsConstantCost 150000
      let memModel = ModelTwoArgumentsConstantCost 4
      pure $ CostingFun cpuModel memModel

equalsByteString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
equalsByteString cpuModelR = do
  cpuModelOnDiagonal <- readModelLinear cpuModelR
  let cpuModel = ModelTwoArgumentsLinearOnDiagonal $ ModelConstantOrLinear 150000
                 (modelLinearSizeIntercept cpuModelOnDiagonal) (modelLinearSizeSlope cpuModelOnDiagonal)
  pure $ CostingFun cpuModel boolMemModel

lessThanByteString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
lessThanByteString cpuModelR = do
  cpuModel <- readModelMinSize cpuModelR
  pure $ CostingFun (ModelTwoArgumentsMinSize cpuModel) boolMemModel

lessThanEqualsByteString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
lessThanEqualsByteString = lessThanByteString


---------------- Cryptography and hashes ----------------

sha2_256 :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
sha2_256 cpuModelR = do
  cpuModel <- readModelLinear cpuModelR
  let memModel = ModelOneArgumentConstantCost (memoryUsageAsCostingInteger $ PlutusHash.sha2 "")
  pure $ CostingFun (ModelOneArgumentLinearCost cpuModel) memModel

sha3_256 :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
sha3_256 cpuModelR = do
  cpuModel <- readModelLinear cpuModelR
  let memModel = ModelOneArgumentConstantCost (memoryUsageAsCostingInteger $ PlutusHash.sha3 "")
  pure $ CostingFun (ModelOneArgumentLinearCost cpuModel) memModel

blake2b :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
blake2b cpuModelR = do
  cpuModel <- readModelLinear cpuModelR
  let memModel = ModelOneArgumentConstantCost (memoryUsageAsCostingInteger $ PlutusHash.blake2b "")
  pure $ CostingFun (ModelOneArgumentLinearCost cpuModel) memModel

-- NB: the R model is based purely on the size of the third argument (since the
-- first two are constant size), so we have to rearrange things a bit to get it to work with
-- a three-argument costing funtion.
verifySignature :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
verifySignature cpuModelR = do
  cpuModel <- readModelLinear cpuModelR
  pure $ CostingFun (ModelThreeArgumentsLinearInZ cpuModel) (ModelThreeArgumentsConstantCost 1)


---------------- Strings ----------------

appendString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
appendString cpuModelR = do
  cpuModel <- ModelTwoArgumentsAddedSizes <$> readModelAddedSizes cpuModelR
  let memModel = ModelTwoArgumentsAddedSizes $ ModelAddedSizes 4 1
  pure $ CostingFun cpuModel memModel

equalsString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
equalsString cpuModelR = do
  cpuModel <- ModelTwoArgumentsLinearOnDiagonal <$> readModelLinearOnDiagonal cpuModelR 100000
  -- TODO: 100000 is a made-up cost for off-diagonal comparisons.  We should put
  -- something more sensible here
  let memModel = boolMemModel
  pure $ CostingFun cpuModel memModel

encodeUtf8 :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
encodeUtf8 cpuModelR = do
  cpuModel <- ModelOneArgumentLinearCost <$> readModelLinear cpuModelR
  let memModel = ModelOneArgumentLinearCost $ ModelLinearSize 4 2
                 -- In the worst case two UTF-16 bytes encode to three UTF-8
                 -- bytes, so two output words per input word should cover that.
  pure $ CostingFun cpuModel memModel

decodeUtf8 :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
decodeUtf8 cpuModelR = do
  cpuModel <- ModelOneArgumentLinearCost <$> readModelLinear cpuModelR
  let memModel = ModelOneArgumentLinearCost $ ModelLinearSize 4 2
                 -- In the worst case one UTF-8 byte decodes to two UTF-16 bytes
  pure $ CostingFun cpuModel memModel


---------------- Bool ----------------

ifThenElse :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
ifThenElse _ =
    pure $ CostingFun (ModelThreeArgumentsConstantCost 1) (ModelThreeArgumentsConstantCost 1)

---------------- Unit ----------------

chooseUnit :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
chooseUnit _ = do
    cpuModel <- ModelTwoArgumentsConstantCost <$> readModelConstantCost cpuModelR
    let memModel = ModelTwoArgumentsConstantCost 4
    pure $ CostingFun cpuModel memModel
-- \() a -> a

---------------- Tracing ----------------

-- ### TODO: get model from R ###
trace :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
trace _ = pure $ CostingFun (ModelTwoArgumentsConstantCost 150000) (ModelTwoArgumentsConstantCost 32)

---------------- Pairs ----------------

-- ### TODO: get model from R ###
fstPair :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
fstPair _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- (x,_) -> x; but with lots of Some's etc.

-- ### TODO: get model from R ###
sndPair :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
sndPair _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- (_,y) -> y; but with lots of Some's etc.


---------------- Lists ----------------

-- ### TODO: get model from R ###
chooseList :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
chooseList _ =
    pure $ CostingFun (ModelThreeArgumentsConstantCost 150000) (ModelThreeArgumentsConstantCost 32)
-- xs a b -> a if xs == [], b otherwise

-- ### TODO: get model from R ###
mkCons :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
mkCons _ =
    pure $ CostingFun (ModelTwoArgumentsConstantCost 150000) (ModelTwoArgumentsConstantCost 32)
-- x xs -> x:xs, but with a dynamic type check

-- ### TODO: get model from R ###
headList :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
headList _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- x:_ -> x, [] -> failure.  Successful case has fromConstant $ someValueOf etc.

-- ### TODO: get model from R ###
tailList :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
tailList _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- Like headList

-- ### TODO: get model from R ###
nullList :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
nullList _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- x::[a] -> Bool

---------------- Data ----------------

-- ### TODO: get model from R ###
chooseData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelSixArguments)
chooseData _ =
      pure $ CostingFun (ModelSixArgumentsConstantCost 150000) (ModelSixArgumentsConstantCost 32)
-- chooseData d p q r s t u  returns one of the last six elements according to what d is.
-- Probably cheap

-- ### TODO: get model from R ###
constrData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
constrData _ =
  pure $ CostingFun (ModelTwoArgumentsConstantCost 150000) (ModelTwoArgumentsConstantCost 32)
-- Just applying Constr

-- ### TODO: get model from R ###
mapData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
mapData _ =
  pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- Just applying Map

-- ### TODO: get model from R ###
listData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
listData _ =
  pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- Just applying List

-- ### TODO: get model from R ###
iData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
iData _ =
  pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- Just applying I

-- ### TODO: get model from R ###
bData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
bData _ =
  pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- Just applying B

-- ### TODO: get model from R ###
unConstrData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
unConstrData _ =
  pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- Constr i ds -> (i,ds);  _ -> fail

-- ### TODO: get model from R ###
unMapData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
unMapData _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- Map es -> es;  _ -> fail

-- ### TODO: get model from R ###
unListData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
unListData _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- List ds -> ds;  _ -> fail

-- ### TODO: get model from R ###
unIData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
unIData _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- I i -> i;  _ -> fail

-- ### TODO: get model from R ###
unBData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
unBData _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- B b -> b;  _ -> fail

equalsData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
equalsData _ = do
  let cpuModel = ModelTwoArgumentsMinSize $ ModelMinSize 150000 10000
  let memModel = ModelTwoArgumentsConstantCost 1
  pure $ CostingFun cpuModel memModel
  {- The size function for 'Data' counts the total number of nodes, and so is
     potentially expensive.  Luckily laziness in the costing functions ensures
     that it's only called if really necessary, so it'll be called here but not
     in 'unBData' etc.  Doing the full traversal seems to increase validation times
     by one or two percent, but we can't really avoid it here. -}


---------------- Misc constructors ----------------

-- ### TODO: get model from R ###
mkPairData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
mkPairData _ =
    pure $ CostingFun (ModelTwoArgumentsConstantCost 150000) (ModelTwoArgumentsConstantCost 32)
-- a b -> (a,b)

-- ### TODO: get model from R ###
mkNilData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
mkNilData _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- () -> [] :: [Data]

-- ### TODO: get model from R ###
mkNilPairData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
mkNilPairData _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 150000) (ModelOneArgumentConstantCost 32)
-- () -> [] :: [(Data,Data)]
