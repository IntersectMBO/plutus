{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import           Foreign.R
-- import qualified Foreign.R.Type as R
import           Control.Exception                                  (TypeError (..))
import           Control.Monad.Catch
import           Data.Aeson
import           Data.Aeson.Encode.Pretty
import qualified Data.ByteString.Lazy                               as BSL
import           Data.Default
import           Data.Either.Extra
import           Data.Text                                          as T
import qualified Data.Text.Encoding                                 as T
import           Data.Vector
import           H.Prelude                                          (MonadR, Region, r)
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.R

main :: IO ()
main = do
  model <- withEmbeddedR defaultConfig $ runRegion $ do
      -- TODO git rev-parse --show-toplevel
      benchData <- [r|
        library(jsonlite)
        source("budgeting-bench/benchData.R")
        benchData("budgeting-bench/csvs/benching.csv")
        |]
      paramAddInteger <- addInteger benchData
      paramSubtractInteger <- subtractInteger benchData
      paramMultiplyInteger <- multiplyInteger benchData
      paramDivideInteger <- divideInteger benchData
      paramQuotientInteger <- quotientInteger benchData
      paramRemainderInteger <- remainderInteger benchData
      paramModInteger <- modInteger benchData
      paramLessThanInteger <- lessThanInteger benchData
      paramLessThanEqInteger <- lessThanEqInteger benchData
      paramGreaterThanInteger <- greaterThanInteger benchData
      paramGreaterThanEqInteger <- greaterThanEqInteger benchData
      paramEqInteger <- eqInteger benchData
      paramConcatenate <- concatenate benchData
      paramTakeByteString <- takeByteString benchData
      paramDropByteString <- dropByteString benchData
      paramSHA2 <- sHA2 benchData
      paramSHA3 <- sHA3 benchData
      paramVerifySignature <- verifySignature benchData
      paramEqByteString <- eqByteString benchData
      paramLtByteString <- ltByteString benchData
      paramGtByteString <- gtByteString benchData
      paramIfThenElse <- ifThenElse benchData

      pure $ CostModel {..}
  BSL.writeFile "language-plutus-core/src/costModel.json" $ encodePretty' (defConfig { confCompare = \_ _-> EQ }) model

filterDF :: MonadR m => Text -> (SomeSEXP (Region m)) -> m (SomeSEXP (Region m))
filterDF by df =
  [r| df_hs %>% filter(BuiltinName %in% c(by_hs))|]

data LinearModelRaw = LinearModelRaw
  { linearModelRawTerm      :: String
  , linearModelRawEstimate  :: Double
  , linearModelRawStdError  :: Double
  , linearModelRawStatistic :: Double
  , linearModelRawPValue    :: Double
  } deriving (Show, Eq)

instance FromJSON LinearModelRaw where
    parseJSON = withObject "LinearModelRaw" $ \v -> LinearModelRaw
        <$> v .: "term"
        <*> v .: "estimate"
        <*> v .: "std.error"
        <*> v .: "statistic"
        <*> v .: "p.value"

findInRaw :: String -> Vector LinearModelRaw -> Either String LinearModelRaw
findInRaw s v = maybeToEither ("Couldn't find the term " <> s) $
  Data.Vector.find (\e -> linearModelRawTerm e == s) v

linearAdditiveModel :: MonadR m => (SomeSEXP (Region m)) -> m (ModelAddedSizes)
linearAdditiveModel df = do
  j <- [r| jsonlite::toJSON(tidy(lm(Mean ~ I(x_mem + y_mem), df_hs))) |]
  let m = do
        model <- eitherDecodeStrict $ T.encodeUtf8 $ (fromSomeSEXP j :: Text)
        intercept <- linearModelRawEstimate <$> findInRaw "(Intercept)" model
        slope <- linearModelRawEstimate <$> findInRaw "I(x_mem + y_mem)" model
        pure $ ModelAddedSizes intercept slope
  case m of
    Left err -> throwM (TypeError err)
    Right x  -> pure x


addInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
addInteger df = do
  addInt <- filterDF "AddInteger" df
  cpuModel <- linearAdditiveModel addInt
  pure $ CostingFun (ModelTwoArgumentsAddedSizes cpuModel) def

subtractInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
subtractInteger _ = pure def
multiplyInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
multiplyInteger _ = pure def
divideInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
divideInteger _ = pure def
quotientInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
quotientInteger _ = pure def
remainderInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
remainderInteger _ = pure def
modInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
modInteger _ = pure def
lessThanInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
lessThanInteger _ = pure def
lessThanEqInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
lessThanEqInteger _ = pure def
greaterThanInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
greaterThanInteger _ = pure def
greaterThanEqInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
greaterThanEqInteger _ = pure def
eqInteger :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
eqInteger _ = pure def
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
