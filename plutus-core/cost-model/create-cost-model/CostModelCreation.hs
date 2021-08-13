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
import           Data.Default
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
    paramTrace                    <- getParams trace  paramTrace
    -- Pairs
    paramFstPair                  <- getParams fstPair  paramFstPair
    paramSndPair                  <- getParams sndPair  paramSndPair
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


-- Currently unused.  Note that something with this cost model could get expensive quickly.
readModelMultipliedSizes :: MonadR m => (SomeSEXP (Region m)) -> m ModelMultipliedSizes
readModelMultipliedSizes model = (pure . uncurry ModelMultipliedSizes) =<< unsafeReadModelFromR "x_mem * y_mem" model

-- Maybe this is too precise.  Even without the `ifelse` we'd still get an upper bound.
readModelSplitConst :: MonadR m => (SomeSEXP (Region m)) -> m ModelSplitConst
readModelSplitConst model = (pure . uncurry ModelSplitConst) =<< unsafeReadModelFromR "ifelse(x_mem > y_mem, I(x_mem * y_mem), 0)" model

readModelConstantCost :: MonadR m => (SomeSEXP (Region m)) -> m CostingInteger
readModelConstantCost model = (\(i, _i) -> pure  i) =<< unsafeReadModelFromR "(Intercept)" model

readModelLinear :: MonadR m => (SomeSEXP (Region m)) -> m ModelLinearSize
readModelLinear model = (\(intercept, slope) -> pure $ ModelLinearSize intercept slope ModelOrientationX) =<< unsafeReadModelFromR "x_mem" model

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
  cpuModel <- readModelSplitConst cpuModelR
  -- GMP requires division (mpn_divrem) to have x - y space.
  -- x - y
  let memModel = ModelTwoArgumentsSubtractedSizes $ ModelSubtractedSizes 0 1 1
  pure $ CostingFun (ModelTwoArgumentsSplitConstMulti cpuModel) memModel

quotientInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
quotientInteger cpuModelR = do
  cpuModel <- readModelSplitConst cpuModelR
  -- Maximum size is the divisor size.
  -- y
  let memModel = ModelTwoArgumentsLinearSize $ ModelLinearSize 0 1 ModelOrientationY
  pure $ CostingFun (ModelTwoArgumentsSplitConstMulti cpuModel) memModel

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
      let cpuModel = ModelAddedSizes 10000 1000  -- 10000 + 1000*(x+y)
      let memModel = ModelTwoArgumentsAddedSizes $ ModelAddedSizes 0 1
      pure $ CostingFun (ModelTwoArgumentsAddedSizes cpuModel) memModel

-- ### TODO: get model from R ###
sliceByteString ::  MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
sliceByteString _ = pure def

-- ### TODO: get model from R ###
lengthOfByteString ::  MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
lengthOfByteString _ = do
      let cpuModel = ModelLinearSize 100000 5000 ModelOrientationX  -- WHAT DOES THIS DO?
      let memModel = ModelOneArgumentConstantCost 4  -- We really want the size of the length here.
      pure $ CostingFun (ModelOneArgumentLinearCost cpuModel) memModel

indexByteString ::  MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
indexByteString _ = pure def

equalsByteString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
equalsByteString cpuModelR = do
  cpuModel <- readModelMinSize cpuModelR
  pure $ CostingFun (ModelTwoArgumentsMinSize cpuModel) boolMemModel

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
  let memModel = ModelOneArgumentConstantCost (memoryUsageAsCostingInteger $ PlutusHash.sha2 "")  -- <---------- Eh?  Yeah, I suppose so.
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

verifySignature :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
verifySignature cpuModelR = do
  cpuModel <- readModelConstantCost cpuModelR
  pure $ CostingFun (ModelThreeArgumentsConstantCost cpuModel) (ModelThreeArgumentsConstantCost 1)


---------------- Strings ----------------

-- ### TODO: get model from R ###
appendString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
appendString _ = pure def
-- We expect this to be linear in x+y (x and y are sizes)

-- ### TODO: get model from R ###
equalsString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
equalsString _ = pure def
-- Like equalsByteString: only expensive on diagonal

-- ### TODO: get model from R ###
encodeUtf8 :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
encodeUtf8 _ = pure def
-- Complicated: one character can be encoded as many bytes and I think we only know the
-- number of characters.  This will need benchmarking with complicate Unicode strings.

-- ### TODO: get model from R ###
decodeUtf8 :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
decodeUtf8 _ = pure def
-- Complicated again.


---------------- Bool ----------------

ifThenElse :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
ifThenElse _ = pure def


---------------- Unit ----------------

-- ### TODO: get model from R ###
chooseUnit :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
chooseUnit _ =
    pure $ CostingFun (ModelTwoArgumentsConstantCost 1) (ModelTwoArgumentsConstantCost 1)

-- \() a -> a;  probably cheap

---------------- Tracing ----------------

-- ### TODO: get model from R ###
trace :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
trace _ = pure def
-- No idea: possibly expensive because of IO.

---------------- Pairs ----------------

-- ### TODO: get model from R ###
fstPair :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
fstPair _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 1)
-- (x,_) -> x; but with lots of Some's etc.

-- ### TODO: get model from R ###
sndPair :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
sndPair _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 1)
-- (_,y) -> y; but with lots of Some's etc.


---------------- Lists ----------------

-- ### TODO: get model from R ###
chooseList :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
chooseList _ =
    pure $ CostingFun (ModelThreeArgumentsConstantCost 1) (ModelThreeArgumentsConstantCost 1)
-- xs a b -> a if xs == [], b otherwise

-- ### TODO: get model from R ###
mkCons :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
mkCons _ =
    pure $ CostingFun (ModelTwoArgumentsConstantCost 1) (ModelTwoArgumentsConstantCost 1)
-- x xs -> x:xs, but with a dynamic type check

-- ### TODO: get model from R ###
headList :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
headList _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 1)
-- x:_ -> x, [] -> failure.  Successful case has fromConstant $ someValueOf etc.

-- ### TODO: get model from R ###
tailList :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
tailList _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 1)
-- Like headList

-- ### TODO: get model from R ###
nullList :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
nullList _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 1)

-- x -> [], same type as x

---------------- Data ----------------

-- ### TODO: get model from R ###
chooseData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelSixArguments)
chooseData _ =
      pure $ CostingFun (ModelSixArgumentsConstantCost 1) (ModelSixArgumentsConstantCost 1)
-- chooseData d p q r s t u  returns one of the last six elements according to what d is.
-- Probably cheap

-- ### TODO: get model from R ###
constrData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
constrData _ =
  pure $ CostingFun (ModelTwoArgumentsConstantCost 1) (ModelTwoArgumentsConstantCost 1)
-- Just applying Constr

-- ### TODO: get model from R ###
mapData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
mapData _ =
  pure $ CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 1)
-- Just applying Map

-- ### TODO: get model from R ###
listData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
listData _ =
  pure $ CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 1)
-- Just applying List

-- ### TODO: get model from R ###
iData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
iData _ =
  pure $ CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 1)
-- Just applying I

-- ### TODO: get model from R ###
bData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
bData _ =
  pure $ CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 1)
-- Just applying B

-- ### TODO: get model from R ###
unConstrData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
unConstrData _ =
  pure $ CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 1)
-- Constr i ds -> (i,ds);  _ -> fail

-- ### TODO: get model from R ###
unMapData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
unMapData _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 1)
-- Map es -> es;  _ -> fail

-- ### TODO: get model from R ###
unListData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
unListData _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 1)
-- List ds -> ds;  _ -> fail

-- ### TODO: get model from R ###
unIData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
unIData _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 1)
-- I i -> i;  _ -> fail

-- ### TODO: get model from R ###
unBData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
unBData _ =
    pure $ CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 1)
-- B b -> b;  _ -> fail

equalsData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
equalsData _ = pure def
-- == : possibly like equalsInteger.  Will it be cheap if the arguments are
-- different sizes? Possibly not.  Do we even know what size is?  AARGH: The
-- size of data is 1!  That's bad, but adding the size to data will maybe
-- require a size on every subobject.  This only matters for == though, since
-- nothing else had to go deep into the object.

---------------- Misc constructors ----------------

-- ### TODO: get model from R ###
mkPairData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
mkPairData _ = pure def
-- a b -> (a,b)

-- ### TODO: get model from R ###
mkNilData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
mkNilData _ = pure def
-- () -> []

-- ### TODO: get model from R ###
mkNilPairData :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
mkNilPairData _ = pure def
-- () -> []
