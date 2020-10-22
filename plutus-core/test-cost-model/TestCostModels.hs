{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

import           Control.Applicative
import           Control.Monad.Morph
import           CostModelCreation
import           Data.Coerce
import           Foreign.R                                          hiding (unsafeCoerce)
import           H.Prelude                                          (MonadR, Region, r)
import           Hedgehog
import qualified Hedgehog.Gen                                       as Gen
import           Hedgehog.Main
import qualified Hedgehog.Range                                     as Range
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.R                                         hiding (unsafeCoerce)
import           Unsafe.Coerce                                      (unsafeCoerce)

prop_addInteger :: Property
prop_addInteger = testPredict addInteger (getConst . paramAddInteger)
prop_subtractInteger :: Property
prop_subtractInteger = testPredict subtractInteger (getConst . paramSubtractInteger)
prop_multiplyInteger :: Property
prop_multiplyInteger = testPredict multiplyInteger (getConst . paramMultiplyInteger)
prop_divideInteger :: Property
prop_divideInteger = testPredict divideInteger (getConst . paramDivideInteger)
prop_quotientInteger :: Property
prop_quotientInteger = testPredict quotientInteger (getConst . paramQuotientInteger)
prop_remainderInteger :: Property
prop_remainderInteger = testPredict remainderInteger (getConst . paramRemainderInteger)
prop_modInteger :: Property
prop_modInteger = testPredict modInteger (getConst . paramModInteger)
prop_lessThanInteger :: Property
prop_lessThanInteger = testPredict lessThanInteger (getConst . paramLessThanInteger)
prop_greaterThanInteger :: Property
prop_greaterThanInteger = testPredict greaterThanInteger (getConst . paramGreaterThanInteger)
prop_lessThanEqInteger :: Property
prop_lessThanEqInteger = testPredict lessThanEqInteger (getConst . paramLessThanEqInteger)
prop_greaterThanEqInteger :: Property
prop_greaterThanEqInteger = testPredict greaterThanEqInteger (getConst . paramGreaterThanEqInteger)
prop_eqInteger :: Property
prop_eqInteger = testPredict eqInteger (getConst . paramEqInteger)
prop_concatenate :: Property
prop_concatenate = testPredict concatenate (getConst . paramConcatenate)
prop_takeByteString :: Property
prop_takeByteString = testPredict takeByteString (getConst . paramTakeByteString)
prop_dropByteString :: Property
prop_dropByteString = testPredict dropByteString (getConst . paramDropByteString)
prop_sha2 :: Property
prop_sha2 = testPredictOne sHA2 (getConst . paramSHA2)
prop_sha3 :: Property
prop_sha3 = testPredictOne sHA3 (getConst . paramSHA3)
prop_verifySignature :: Property
prop_verifySignature = testPredictThree verifySignature (getConst . paramVerifySignature)
prop_eqByteString :: Property
prop_eqByteString = testPredict eqByteString (getConst . paramEqByteString)
prop_ltByteString :: Property
prop_ltByteString = testPredict ltByteString (getConst . paramLtByteString)
prop_gtByteString :: Property
prop_gtByteString = testPredict gtByteString (getConst . paramGtByteString)
-- prop_ifThenElse :: Property
-- prop_ifThenElse = testPredict ifThenElse (getConst . paramIfThenElse)

-- Runs property tests in the `R` Monad.
propertyR :: PropertyT (R s) () -> Property
-- Why all the unsafe, you ask? `runRegion` (from inline-r) has a `(forall s. R s
-- a)` to ensure no `R` types leave the scope. Additionally, it has an `NFData`
-- constraint to ensure no unexecuted R code escapes. `unsafeRunRegion` does away
-- with the first constraint. However, consuring up a `NFData` constraint for
-- `PropertyT` is impossible, because internally, `PropertyT` constructs a `TreeT`
-- to hold all the branches for reduction. These branches will contain `(R s)`,
-- which has a `MonadIO` instance. No `NFData` for `IO`, so no `NFData` for
-- `TreeT`. For now, this didn't crash yet.
propertyR prop = withTests 20 $ property $ unsafeHoist unsafeRunRegion prop
  where
    unsafeHoist :: (MFunctor t, Monad m) => (m () -> n ()) -> t m () -> t n ()
    unsafeHoist nt = hoist (unsafeCoerce nt)

-- Creates the model on the R side, loads the parameters over to Haskell, and runs both models with a bunch of ExMemory combinations and compares the outputs.
testPredict :: ((SomeSEXP (Region (R s))) -> (R s) (CostingFun ModelTwoArguments))
  -> ((CostModelBase (Const (SomeSEXP (Region (R s))))) -> SomeSEXP s)
  -> Property
testPredict haskellModelFun modelFun = propertyR $ do
  modelR <- lift $ costModelsR
  modelH <- lift $ haskellModelFun $ modelFun modelR
  let
    predictR :: MonadR m => Integer -> Integer -> m Integer
    predictR x y =
      let
        xD = fromInteger x :: Double
        yD = fromInteger y :: Double
        model = modelFun modelR
      in
        (\t -> ceiling $ (fromSomeSEXP t :: Double)) <$> [r|predict(model_hs, data.frame(x_mem=xD_hs, y_mem=yD_hs))[[1]]|]
    predictH :: Integer -> Integer -> Integer
    predictH x y = coerce $ _exBudgetCPU $ runCostingFunTwoArguments modelH (ExMemory x) (ExMemory y)
    sizeGen = do
      y <- Gen.integral (Range.exponential 0 5000)
      x <- Gen.integral (Range.exponential 0 5000)
      pure (x, y)
  (x, y) <- forAll sizeGen
  byR <- lift $ predictR x y
  diff byR (>) 0
  byR === predictH x y

testPredictOne :: ((SomeSEXP (Region (R s))) -> (R s) (CostingFun ModelOneArgument))
  -> ((CostModelBase (Const (SomeSEXP (Region (R s))))) -> SomeSEXP s)
  -> Property
testPredictOne haskellModelFun modelFun = propertyR $ do
  modelR <- lift $ costModelsR
  modelH <- lift $ haskellModelFun $ modelFun modelR
  let
    predictR :: MonadR m => Integer -> m Integer
    predictR x =
      let
        xD = fromInteger x :: Double
        model = modelFun modelR
      in
        (\t -> ceiling $ (fromSomeSEXP t :: Double)) <$> [r|predict(model_hs, data.frame(x_mem=xD_hs))[[1]]|]
    predictH :: Integer -> Integer
    predictH x = coerce $ _exBudgetCPU $ runCostingFunOneArgument modelH (ExMemory x)
    sizeGen = do
      x <- Gen.integral (Range.exponential 0 5000)
      pure x
  x <- forAll sizeGen
  byR <- lift $ predictR x
  diff byR (>) 0
  byR === predictH x

testPredictThree :: ((SomeSEXP (Region (R s))) -> (R s) (CostingFun ModelThreeArguments))
  -> ((CostModelBase (Const (SomeSEXP (Region (R s))))) -> SomeSEXP s)
  -> Property
testPredictThree haskellModelFun modelFun = propertyR $ do
  modelR <- lift $ costModelsR
  modelH <- lift $ haskellModelFun $ modelFun modelR
  let
    predictR :: MonadR m => Integer -> Integer -> Integer -> m Integer
    predictR x y _z =
      let
        xD = fromInteger x :: Double
        yD = fromInteger y :: Double
        -- zD = fromInteger z :: Double
        model = modelFun modelR
      in
        (\t -> ceiling $ (fromSomeSEXP t :: Double)) <$> [r|predict(model_hs, data.frame(x_mem=xD_hs, y_mem=yD_hs))[[1]]|]
    predictH :: Integer -> Integer -> Integer -> Integer
    predictH x y z = coerce $ _exBudgetCPU $ runCostingFunThreeArguments modelH (ExMemory x) (ExMemory y) (ExMemory z)
    sizeGen = do
      y <- Gen.integral (Range.exponential 0 5000)
      x <- Gen.integral (Range.exponential 0 5000)
      z <- Gen.integral (Range.exponential 0 5000)
      pure (x, y, z)
  (x, y, z) <- forAll sizeGen
  byR <- lift $ predictR x y z
  diff byR (>) 0
  byR === predictH x y z

main :: IO ()
main =  withEmbeddedR defaultConfig $ defaultMain $ [checkSequential $$(discover)]
