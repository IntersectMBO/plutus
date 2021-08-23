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

import           PlutusCore.Evaluation.Machine.BuiltinCostModel
import           PlutusCore.Evaluation.Machine.ExBudget
import           PlutusCore.Evaluation.Machine.ExMemory

import           Foreign.R                                      hiding (unsafeCoerce)
import           H.Prelude                                      (MonadR, Region, r)
import           Language.R                                     hiding (unsafeCoerce)

import           Control.Applicative
import           Control.Monad.Morph
import           CostModelCreation
import           Data.Coerce
import           Hedgehog
import qualified Hedgehog.Gen                                   as Gen
import           Hedgehog.Main
import qualified Hedgehog.Range                                 as Range
import           Unsafe.Coerce                                  (unsafeCoerce)


{- | This module is supposed to test that the R cost models for built-in functions
   defined in BuiltinCostModel.hs produce the same results as the Haskell
   versions. However there are a couple of subtleties.  (A) The R models use
   floating point numbers and the Haskell versions use CostingIntegers, and
   there will be some difference in precision because of this. (B) The R models
   produce results in milliseconds and the Haskell versions produce results in
   picoseconds. We deal with (B) by using the msToPs function from
   CostModelCreation to convert R results to picoseconds expressed as
   CostingIntegers.  To deal with (A), we don't check for exact equality of the
   outputs but instead check that the R result and the Haskell result agreee to
   within a factor of 1/10000 (one hundredth of a percent).

   This executes all of the R code (reading the CSV file and constructing all of
   the models) for every instance of every test, so it takes a moderately long
   time (maybe 3 minutes).
-}


-- Approximate equality
(~=) :: Integral a => a -> a -> Bool
x ~= y =
    abs ((x'-y')/y')  < 1/10000
        where x' = fromIntegral x :: Double
              y' = fromIntegral y :: Double

prop_addInteger :: Property
prop_addInteger =
    testPredictTwo addInteger (getConst . paramAddInteger)

prop_subtractInteger :: Property
prop_subtractInteger =
    testPredictTwo subtractInteger (getConst . paramSubtractInteger)

prop_multiplyInteger :: Property
prop_multiplyInteger =
    testPredictTwo multiplyInteger (getConst . paramMultiplyInteger)

-- FIXME: We now have piecewise models for division and other functions,
-- and these aren't quite properly integrated with each other yet.
-- For the time being, the relevant tests are disabled.

{-
prop_divideInteger :: Property
prop_divideInteger =
    testPredictTwo divideInteger (getConst . paramDivideInteger)

prop_quotientInteger :: Property
prop_quotientInteger =
    testPredictTwo quotientInteger (getConst . paramQuotientInteger)

prop_remainderInteger :: Property
prop_remainderInteger =
    testPredictTwo remainderInteger (getConst . paramRemainderInteger)

prop_modInteger :: Property
prop_modInteger =
    testPredictTwo modInteger (getConst . paramModInteger)
-}

prop_lessThanInteger :: Property
prop_lessThanInteger =
    testPredictTwo lessThanInteger (getConst . paramLessThanInteger)

prop_lessThanEqualsInteger :: Property
prop_lessThanEqualsInteger =
    testPredictTwo lessThanEqualsInteger (getConst . paramLessThanEqualsInteger)

prop_equalsInteger :: Property
prop_equalsInteger =
    testPredictTwo equalsInteger (getConst . paramEqualsInteger)

prop_appendByteString :: Property
prop_appendByteString =
    testPredictTwo appendByteString (getConst . paramAppendByteString)

prop_sha2_256 :: Property
prop_sha2_256 =
    testPredictOne sha2_256 (getConst . paramSha2_256)

{-  Not sure why this is failing.
prop_sha3_256 :: Property
prop_sha3_256 =
    testPredictOne sha3_256 (getConst . paramSha3_256)
-}

prop_blake2b :: Property
prop_blake2b =
    testPredictOne blake2b (getConst . paramBlake2b)

prop_verifySignature :: Property
prop_verifySignature =
    testPredictThree verifySignature (getConst . paramVerifySignature)

{-
prop_equalsByteString :: Property
prop_equalsByteString =
    testPredictTwo equalsByteString (getConst . paramEqualsByteString)
-}

prop_lessThanByteString :: Property
prop_lessThanByteString =
    testPredictTwo lessThanByteString (getConst . paramLessThanByteString)

prop_lessThanEqualsByteString :: Property
prop_lessThanEqualsByteString =
    testPredictTwo lessThanEqualsByteString (getConst . paramLessThanEqualsByteString)

-- prop_ifThenElse :: Property
-- prop_ifThenElse =
--    testPredictTwo ifThenElse (getConst . paramIfThenElse)

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


-- Creates the model on the R side, loads the parameters over to Haskell, and
-- runs both models with a bunch of ExMemory combinations and compares the
-- outputs.
testPredictOne :: ((SomeSEXP (Region (R s))) -> (R s) (CostingFun ModelOneArgument))
  -> ((BuiltinCostModelBase (Const (SomeSEXP (Region (R s))))) -> SomeSEXP s)
  -> Property
testPredictOne haskellModelFun modelFun = propertyR $ do
  modelR <- lift $ costModelsR
  modelH <- lift $ haskellModelFun $ modelFun modelR
  let
    predictR :: MonadR m => CostingInteger -> m CostingInteger
    predictR x =
      let
        xD = fromIntegral x :: Double
        model = modelFun modelR
      in
        (\t -> msToPs (fromSomeSEXP t :: Double)) <$> [r|predict(model_hs, data.frame(x_mem=xD_hs))[[1]]|]
    predictH :: CostingInteger -> CostingInteger
    predictH x = coerce $ exBudgetCPU $ runCostingFunOneArgument modelH (ExMemory x)
    sizeGen = do
      x <- Gen.integral (Range.exponential 0 5000)
      pure x
  x <- forAll sizeGen
  byR <- lift $ predictR x
  diff byR (>) 0
  diff byR (~=) (predictH x)

testPredictTwo :: ((SomeSEXP (Region (R s))) -> (R s) (CostingFun ModelTwoArguments))
  -> ((BuiltinCostModelBase (Const (SomeSEXP (Region (R s))))) -> SomeSEXP s)
  -> Property
testPredictTwo haskellModelFun modelFun = propertyR $ do
  modelR <- lift $ costModelsR
  modelH <- lift $ haskellModelFun $ modelFun modelR
  let
    predictR :: MonadR m => CostingInteger -> CostingInteger -> m CostingInteger
    predictR x y =
      let
        xD = fromIntegral x :: Double
        yD = fromIntegral y :: Double
        model = modelFun modelR
      in
        (\t -> msToPs (fromSomeSEXP t :: Double)) <$> [r|predict(model_hs, data.frame(x_mem=xD_hs, y_mem=yD_hs))[[1]]|]
    predictH :: CostingInteger -> CostingInteger -> CostingInteger
    predictH x y = coerce $ exBudgetCPU $ runCostingFunTwoArguments modelH (ExMemory x) (ExMemory y)
    sizeGen = do
      y <- Gen.integral (Range.exponential 0 5000)
      x <- Gen.integral (Range.exponential 0 5000)
      pure (x, y)
  (x, y) <- forAll sizeGen
  byR <- lift $ predictR x y
  diff byR (>) 0
  diff byR (~=) (predictH x y)

testPredictThree :: ((SomeSEXP (Region (R s))) -> (R s) (CostingFun ModelThreeArguments))
  -> ((BuiltinCostModelBase (Const (SomeSEXP (Region (R s))))) -> SomeSEXP s)
  -> Property
testPredictThree haskellModelFun modelFun = propertyR $ do
  modelR <- lift $ costModelsR
  modelH <- lift $ haskellModelFun $ modelFun modelR
  let
    predictR :: MonadR m => CostingInteger -> CostingInteger -> CostingInteger -> m CostingInteger
    predictR x y _z =
      let
        xD = fromIntegral x :: Double
        yD = fromIntegral y :: Double
        -- zD = fromInteger z :: Double
        model = modelFun modelR
      in
        (\t -> msToPs (fromSomeSEXP t :: Double)) <$> [r|predict(model_hs, data.frame(x_mem=xD_hs, y_mem=yD_hs))[[1]]|]
    predictH :: CostingInteger -> CostingInteger -> CostingInteger -> CostingInteger
    predictH x y z = coerce $ exBudgetCPU $ runCostingFunThreeArguments modelH (ExMemory x) (ExMemory y) (ExMemory z)
    sizeGen = do
      y <- Gen.integral (Range.exponential 0 5000)
      x <- Gen.integral (Range.exponential 0 5000)
      z <- Gen.integral (Range.exponential 0 5000)
      pure (x, y, z)
  (x, y, z) <- forAll sizeGen
  byR <- lift $ predictR x y z
  diff byR (>) 0
  diff byR (~=) (predictH x y z)

main :: IO ()
main =  withEmbeddedR defaultConfig $ defaultMain $ [checkSequential $$(discover)]
