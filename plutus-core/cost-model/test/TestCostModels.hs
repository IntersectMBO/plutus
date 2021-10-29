{-# LANGUAGE BangPatterns        #-}
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

import           CostModelCreation

import           Control.Applicative                            (Const, getConst)
import           Control.Monad.Morph                            (MFunctor, hoist, lift)
import           Data.Coerce                                    (coerce)
import           Unsafe.Coerce                                  (unsafeCoerce)

import           H.Prelude                                      (MonadR)
import           Language.R                                     as R (R, SomeSEXP, defaultConfig, fromSomeSEXP,
                                                                      unsafeRunRegion, withEmbeddedR)
import           Language.R.QQ                                  (r)

import           Hedgehog                                       (Gen, Group (..), Property, PropertyT, checkSequential,
                                                                 diff, forAll, property, withTests)
import qualified Hedgehog.Gen                                   as Gen
import qualified Hedgehog.Main                                  as HH (defaultMain)
import qualified Hedgehog.Range                                 as Range

-- import           Debug.Trace

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
   within a factor of 1/100 (one percent).

-}

-- | Generate inputs for costing functions, making sure that we test a large
-- range of inputs, but that we also get small inputs.
memUsageGen :: Gen CostingInteger
memUsageGen =
    Gen.choice [small, largish]
        where small   = Gen.integral (Range.constant 0 2)
              largish = Gen.integral (Range.linear 0 5000)

-- A type alias to make our signatures more concise.  This type is a record in
-- which every field refers to an R SEXP (over some state s), the lm model for
-- the benchmark data for the relevant builtin.
type RModels s = BuiltinCostModelBase (Const (SomeSEXP s))

{- The region where we want to carry out tests for a two-dimensional model.  The
   Haskell versions of some of these models are defined in several pieces and we
   don't yet have corresponding piecewise R models, so we just restrict to the
   places where the piecewise models are interesting (they're typically constant
   elsewhere). -}
data TestDomain =
    Everywhere
  | OnDiagonal
  | BelowDiagonal

-- Approximate equality
(~=) :: Integral a => a -> a -> Bool
x ~= y
  | x==0 && y==0 = True
  | otherwise = -- Debug.Trace.trace ("err = " ++ show (err * 100)) $
                err < 1/100
    where x' = fromIntegral x :: Double
          y' = fromIntegral y :: Double
          err = abs ((x'-y')/y')


-- Properties for individual builtins

prop_addInteger :: RModels s -> Property
prop_addInteger =
    testPredictTwo Everywhere addInteger . paramAddInteger

prop_subtractInteger :: RModels s -> Property
prop_subtractInteger =
    testPredictTwo Everywhere subtractInteger . paramSubtractInteger

prop_multiplyInteger :: RModels s -> Property
prop_multiplyInteger =
    testPredictTwo Everywhere multiplyInteger . paramMultiplyInteger

prop_divideInteger :: RModels s -> Property
prop_divideInteger =
    testPredictTwo BelowDiagonal divideInteger . paramDivideInteger

prop_quotientInteger :: RModels s -> Property
prop_quotientInteger =
    testPredictTwo BelowDiagonal quotientInteger . paramQuotientInteger

prop_remainderInteger :: RModels s -> Property
prop_remainderInteger =
    testPredictTwo BelowDiagonal remainderInteger . paramRemainderInteger

prop_modInteger :: RModels s -> Property
prop_modInteger =
    testPredictTwo BelowDiagonal modInteger . paramModInteger

prop_lessThanInteger :: RModels s -> Property
prop_lessThanInteger =
    testPredictTwo Everywhere lessThanInteger . paramLessThanInteger

prop_lessThanEqualsInteger :: RModels s -> Property
prop_lessThanEqualsInteger =
    testPredictTwo Everywhere lessThanEqualsInteger . paramLessThanEqualsInteger

prop_equalsInteger :: RModels s -> Property
prop_equalsInteger =
    testPredictTwo Everywhere equalsInteger . paramEqualsInteger

prop_appendByteString :: RModels s -> Property
prop_appendByteString =
    testPredictTwo Everywhere appendByteString . paramAppendByteString

prop_sha2_256 :: RModels s -> Property
prop_sha2_256 =
    testPredictOne sha2_256 . paramSha2_256

prop_sha3_256 :: RModels s -> Property
prop_sha3_256 =
    testPredictOne sha3_256 . paramSha3_256

prop_blake2b :: RModels s -> Property
prop_blake2b =
    testPredictOne blake2b . paramBlake2b

prop_verifySignature :: RModels s -> Property
prop_verifySignature =
    testPredictThree verifySignature . paramVerifySignature

prop_equalsByteString :: RModels s -> Property
prop_equalsByteString =
    testPredictTwo OnDiagonal equalsByteString . paramEqualsByteString

prop_lessThanByteString :: RModels s -> Property
prop_lessThanByteString =
    testPredictTwo Everywhere lessThanByteString . paramLessThanByteString

prop_lessThanEqualsByteString :: RModels s -> Property
prop_lessThanEqualsByteString =
    testPredictTwo Everywhere lessThanEqualsByteString . paramLessThanEqualsByteString

prop_ifThenElse :: RModels s -> Property
prop_ifThenElse =
    testPredictThree ifThenElse . paramIfThenElse


-- Testing the properties

-- Runs property tests in the `R` Monad.
propertyR :: PropertyT (R s) () -> Property
-- Why all the unsafe, you ask? `runRegion` (from inline-r) has a `(forall s. R s
-- a)` to ensure no `R` types leave the scope. Additionally, it has an `NFData`
-- constraint to ensure no unexecuted R code escapes. `unsafeRunRegion` does away
-- with the first constraint. However, conjuring up a `NFData` constraint for
-- `PropertyT` is impossible, because internally, `PropertyT` constructs a `TreeT`
-- to hold all the branches for reduction. These branches will contain `(R s)`,
-- which has a `MonadIO` instance. No `NFData` for `IO`, so no `NFData` for
-- `TreeT`. For now, this didn't crash yet.
propertyR prop = withTests 100 $ property $ unsafeHoist unsafeRunRegion prop
  where
    unsafeHoist :: (MFunctor t, Monad m) => (m () -> n ()) -> t m () -> t n ()
    unsafeHoist nt = hoist (unsafeCoerce nt)

-- Creates the model on the R side, loads the parameters over to Haskell, and
-- runs both models with a bunch of ExMemory combinations and compares the
-- outputs.
testPredictOne
    :: (SomeSEXP s -> R s (CostingFun ModelOneArgument))
    -> Const (SomeSEXP s) a
    -> Property
testPredictOne haskellModelFun modelR1 = propertyR $ do
  let modelR = getConst modelR1
  modelH <- lift $ haskellModelFun modelR
  let
    predictR :: MonadR m => CostingInteger -> m CostingInteger
    predictR x =
      let
        xD = fromIntegral x :: Double
      in
       msToPs . fromSomeSEXP <$> [r|predict(modelR_hs, data.frame(x_mem=xD_hs))[[1]]|]
    predictH :: CostingInteger -> CostingInteger
    predictH x = coerce $ exBudgetCPU $ runCostingFunOneArgument modelH (ExMemory x)
    sizeGen = memUsageGen
  x <- forAll sizeGen
  byR <- lift $ predictR x
  diff byR (>=) 0  -- Sometimes R gives us models which pass through the origin, so we have to allow zero cost becase of that
  diff byR (~=) (predictH x)

testPredictTwo
    :: forall s a . TestDomain
    -> (SomeSEXP s -> R s (CostingFun ModelTwoArguments))
    -> Const (SomeSEXP s) a
    -> Property
testPredictTwo domain haskellModelFun modelR1 = propertyR $ do
  let modelR = getConst modelR1
  modelH <- lift $ haskellModelFun modelR
  let
    predictR :: MonadR m => CostingInteger -> CostingInteger -> m CostingInteger
    predictR x y =
      let
        xD = fromIntegral x :: Double
        yD = fromIntegral y :: Double
      in
        msToPs . fromSomeSEXP <$> [r|predict(modelR_hs, data.frame(x_mem=xD_hs, y_mem=yD_hs))[[1]]|]
    predictH :: CostingInteger -> CostingInteger -> CostingInteger
    predictH x y = coerce $ exBudgetCPU $ runCostingFunTwoArguments modelH (ExMemory x) (ExMemory y)
    sizeGen = case domain of
                Everywhere    -> twoArgs
                OnDiagonal    -> memUsageGen >>= \x -> pure (x,x)
                BelowDiagonal -> Gen.filter (uncurry (>=)) twoArgs
        where twoArgs = (,) <$> memUsageGen <*> memUsageGen
  (x, y) <- forAll sizeGen
  byR <- lift $ predictR x y
  diff byR (>=) 0
  diff byR (~=) (predictH x y)

testPredictThree
    :: (SomeSEXP s -> R s (CostingFun ModelThreeArguments))
    -> Const (SomeSEXP s) a
    -> Property
testPredictThree haskellModelFun modelR1 = propertyR $ do
  let modelR = getConst modelR1
  modelH <- lift $ haskellModelFun modelR
  let
    predictR :: MonadR m => CostingInteger -> CostingInteger -> CostingInteger -> m CostingInteger
    predictR x y _z =
      let
        xD = fromIntegral x :: Double
        yD = fromIntegral y :: Double
        -- zD = fromInteger z :: Double
      in
        msToPs . fromSomeSEXP <$> [r|predict(modelR_hs, data.frame(x_mem=xD_hs, y_mem=yD_hs))[[1]]|]
    predictH :: CostingInteger -> CostingInteger -> CostingInteger -> CostingInteger
    predictH x y z = coerce $ exBudgetCPU $ runCostingFunThreeArguments modelH (ExMemory x) (ExMemory y) (ExMemory z)
    sizeGen = (,,) <$> memUsageGen <*> memUsageGen <*> memUsageGen
  (x, y, z) <- forAll sizeGen
  byR <- lift $ predictR x y z
  diff byR (>=) 0
  diff byR (~=) (predictH x y z)

-- TODO: discover the properties automatically.  $$(discover) doesn't work
-- because it expects to find Properties, but we have to apply each prop_xyz to
-- 'models' to get a Property
main :: IO ()
main =
    withEmbeddedR R.defaultConfig $ do
      models <- unsafeRunRegion costModelsR
      let tests =
              [ ("addInteger",               prop_addInteger               models)
              , ("subtractInteger",          prop_subtractInteger          models)
              , ("multiplyInteger",          prop_multiplyInteger          models)
              , ("divideInteger",            prop_divideInteger            models)
              , ("quotientInteger",          prop_quotientInteger          models)
              , ("remainderInteger",         prop_remainderInteger         models)
              , ("modInteger",               prop_modInteger               models)
              , ("lessThanInteger",          prop_lessThanInteger          models)
              , ("lessThanEqualsInteger",    prop_lessThanEqualsInteger    models)
              , ("equalsInteger",            prop_equalsInteger            models)
              , ("equalsByteString",         prop_equalsByteString         models)
              , ("appendByteString",         prop_appendByteString         models)
              , ("lessThanByteString",       prop_lessThanByteString       models)
              , ("lessThanEqualsByteString", prop_lessThanEqualsByteString models)
              , ("sha2_256",                 prop_sha2_256                 models)
              , ("sha3_256",                 prop_sha3_256                 models)
              , ("blake2b",                  prop_blake2b                  models)
              , ("verifySignature",          prop_verifySignature          models)
              , ("ifThenElse",               prop_ifThenElse               models)
              ]
      HH.defaultMain $ [checkSequential $ Group "Builtin model tests" tests]
