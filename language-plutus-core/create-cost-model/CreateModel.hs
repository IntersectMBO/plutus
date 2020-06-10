{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import           Control.Exception                                  (TypeError (..))
import           Control.Monad.Catch
import           Data.Aeson.Encode.Pretty
import qualified Data.ByteString.Lazy                               as BSL
import           Data.Csv
import           Data.Default
import           Data.Either.Extra
import           Data.Text                                          as T
import qualified Data.Text.Encoding                                 as T
import           Data.Vector
import           Foreign.R
import           GHC.Generics
import           H.Prelude                                          (MonadR, Region, r)
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.R

{- See Note [Creation of the Cost Model]
-}

main :: IO ()
main = do
  model <- withEmbeddedR defaultConfig $ runRegion $ do
      models <- [r|
        library(jsonlite)
        source("budgeting-bench/models.R")
        modelFun("budgeting-bench/csvs/benching.csv")
      |]
      paramAddInteger <- addInteger models
      paramSubtractInteger <- subtractInteger models
      paramMultiplyInteger <- multiplyInteger models
      paramDivideInteger <- divideInteger models
      paramQuotientInteger <- quotientInteger models
      paramRemainderInteger <- remainderInteger models
      paramModInteger <- modInteger models
      paramLessThanInteger <- lessThanInteger models
      paramLessThanEqInteger <- lessThanEqInteger models
      paramGreaterThanInteger <- greaterThanInteger models
      paramGreaterThanEqInteger <- greaterThanEqInteger models
      paramEqInteger <- eqInteger models
      paramConcatenate <- concatenate models
      paramTakeByteString <- takeByteString models
      paramDropByteString <- dropByteString models
      paramSHA2 <- sHA2 models
      paramSHA3 <- sHA3 models
      paramVerifySignature <- verifySignature models
      paramEqByteString <- eqByteString models
      paramLtByteString <- ltByteString models
      paramGtByteString <- gtByteString models
      paramIfThenElse <- ifThenElse models

      pure $ CostModel {..}
  BSL.writeFile "language-plutus-core/src/costModel.json" $ encodePretty' (defConfig { confCompare = \_ _-> EQ }) model

filterDF :: MonadR m => Text -> (SomeSEXP (Region m)) -> m (SomeSEXP (Region m))
filterDF by df =
  [r| df_hs %>% filter(BuiltinName %in% c(by_hs))|]

data LinearModelRaw = LinearModelRaw
  { linearModelIndex        :: Integer
  , linearModelRawTerm      :: String
  , linearModelRawEstimate  :: Double
  , linearModelRawStdError  :: Double
  , linearModelRawStatistic :: Double
  , linearModelRawPValue    :: Double
  } deriving (Show, Eq, Generic)

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
findInRaw s v = maybeToEither ("Couldn't find the term " <> s) $
  Data.Vector.find (\e -> linearModelRawTerm e == s) v

unsafeReadModelFromR :: MonadR m => String -> (SomeSEXP (Region m)) -> m (Double, Double)
unsafeReadModelFromR formula rmodel = do
  j <- [r| write.csv(tidy(rmodel_hs), file=textConnection("out", "w", local=TRUE))
          paste(out, collapse="\n") |]
  let m = do
        model <- Data.Csv.decode HasHeader $ BSL.fromStrict $ T.encodeUtf8 $ (fromSomeSEXP j :: Text)
        intercept <- linearModelRawEstimate <$> findInRaw "(Intercept)" model
        slope <- linearModelRawEstimate <$> findInRaw formula model
        pure $ (intercept, slope)
  case m of
    Left err -> throwM (TypeError err)
    Right x  -> pure x

unsafeReadModelFromR2 :: MonadR m => String -> String -> (SomeSEXP (Region m)) -> m (Double, Double, Double)
unsafeReadModelFromR2 formula1 formula2 rmodel = do
  j <- [r| write.csv(tidy(rmodel_hs), file=textConnection("out", "w", local=TRUE))
          paste(out, collapse="\n") |]
  let m = do
        model <- Data.Csv.decode HasHeader $ BSL.fromStrict $ T.encodeUtf8 $ (fromSomeSEXP j :: Text)
        intercept <- linearModelRawEstimate <$> findInRaw "(Intercept)" model
        slope1 <- linearModelRawEstimate <$> findInRaw formula1 model
        slope2 <- linearModelRawEstimate <$> findInRaw formula2 model
        pure $ (intercept, slope1, slope2)
  case m of
    Left err -> throwM (TypeError err)
    Right x  -> pure x

readModelAddedSizes :: MonadR m => (SomeSEXP (Region m)) -> String -> m ModelAddedSizes
readModelAddedSizes models name = (pure . uncurry ModelAddedSizes) =<< unsafeReadModelFromR "I(x_mem + y_mem)" =<< ([r| models_hs[[name_hs]]|])

readModelMinSize :: MonadR m => (SomeSEXP (Region m)) -> String -> m ModelMinSize
readModelMinSize models name = (pure . uncurry ModelMinSize) =<< unsafeReadModelFromR "I(pmin(x_mem, y_mem))" =<< ([r| models_hs[[name_hs]]|])

uncurry3 :: (a -> b -> c -> d) -> ((a, b, c) -> d)
uncurry3 f ~(a,b,c) = f a b c

readModelExpSizes :: MonadR m => (SomeSEXP (Region m)) -> String -> m ModelExpSizes
readModelExpSizes models name = (pure . uncurry3 ModelExpSizes) =<< unsafeReadModelFromR2 "x_mem" "y_mem" =<< ([r| models_hs[[name_hs]]|])

readModelSplitConst :: MonadR m => (SomeSEXP (Region m)) -> String -> m ModelSplitConst
readModelSplitConst models name = (pure . uncurry ModelSplitConst) =<< unsafeReadModelFromR "ifelse(x_mem > y_mem, x_mem + y_mem, 0)" =<< ([r| models_hs[[name_hs]]|])

addInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
addInteger models = do
  cpuModel <- readModelAddedSizes models "addIntegerModel"
  pure $ CostingFun (ModelTwoArgumentsAddedSizes cpuModel) def

subtractInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
subtractInteger models = do
  cpuModel <- readModelAddedSizes models "subtractIntegerModel"
  pure $ CostingFun (ModelTwoArgumentsAddedSizes cpuModel) def

multiplyInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
multiplyInteger models = do
  cpuModel <- readModelExpSizes models "multiplyIntegerModel"
  pure $ CostingFun (ModelTwoArgumentsExpMultiSizes cpuModel) def

divideInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
divideInteger models = do
  cpuModel <- readModelSplitConst models "divideIntegerModel"
  pure $ CostingFun (ModelTwoArgumentsSplitConstMulti cpuModel) def

quotientInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
quotientInteger = divideInteger
remainderInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
remainderInteger = divideInteger
modInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
modInteger = divideInteger

lessThanInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
lessThanInteger models = do
  cpuModel <- readModelMinSize models "lessThanIntegerModel"
  pure $ CostingFun (ModelTwoArgumentsMinSize cpuModel) def
greaterThanInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
greaterThanInteger = lessThanInteger

lessThanEqInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
lessThanEqInteger models = do
  cpuModel <- readModelMinSize models "lessThanEqIntegerModel"
  pure $ CostingFun (ModelTwoArgumentsMinSize cpuModel) def
greaterThanEqInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
greaterThanEqInteger = lessThanEqInteger

eqInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
eqInteger models = do
  cpuModel <- readModelMinSize models "eqIntegerModel"
  pure $ CostingFun (ModelTwoArgumentsMinSize cpuModel) def

concatenate :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
concatenate _ = pure def
takeByteString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
takeByteString _ = pure def
dropByteString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
dropByteString _ = pure def
sHA2 :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
sHA2 _ = pure def
sHA3 :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelOneArgument)
sHA3 _ = pure def
verifySignature :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
verifySignature _ = pure def
eqByteString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
eqByteString _ = pure def
ltByteString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
ltByteString _ = pure def
gtByteString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
gtByteString _ = pure def
ifThenElse :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelThreeArguments)
ifThenElse _ = pure def
