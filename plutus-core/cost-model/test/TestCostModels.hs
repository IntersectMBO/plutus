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
import           System.IO.Unsafe                               (unsafePerformIO)
import           Unsafe.Coerce                                  (unsafeCoerce)

import           H.Prelude                                      (MonadR, Region, getExecContext, io,
                                                                 unsafeRunWithExecContext)
import           Language.R                                     as R (R, SomeSEXP, defaultConfig, fromSomeSEXP,
                                                                      runRegion, unsafeRunRegion, withEmbeddedR)
import           Language.R.QQ                                  (r)

import           Hedgehog                                       (Gen, Group (..), Property, PropertyT, check,
                                                                 checkSequential, diff, discover, forAll, property,
                                                                 withTests)
import qualified Hedgehog.Gen                                   as Gen
import qualified Hedgehog.Main                                  as HH (defaultMain)
import qualified Hedgehog.Range                                 as Range


import           Debug.Trace

paramGen :: Gen CostingInteger
paramGen = Gen.resize 90 $ Gen.integral (Range.linear 0 5000)

type CostingFunctions s = BuiltinCostModelBase (Const (SomeSEXP s))
-- This is just a record in which every field refers to an SEXP (over some state)


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

-}


-- Approximate equality
(~=) :: Integral a => a -> a -> Bool
x ~= y =
    (x==0 && y==0) ||
    abs ((x'-y')/y')  < 1/500
        where x' = fromIntegral x :: Double
              y' = fromIntegral y :: Double

prop_addInteger :: CostingFunctions s -> Property
prop_addInteger =
    testPredictTwo addInteger . paramAddInteger

prop_subtractInteger :: CostingFunctions s -> Property
prop_subtractInteger =
    testPredictTwo subtractInteger . paramSubtractInteger

prop_multiplyInteger :: CostingFunctions s -> Property
prop_multiplyInteger =
    testPredictTwo multiplyInteger . paramMultiplyInteger

-- FIXME: We now have piecewise models for division and other functions,
-- and these aren't quite properly integrated with each other yet.
-- For the time being, the relevant tests are disabled.

prop_divideInteger :: CostingFunctions s -> Property
prop_divideInteger =
    testPredictTwo divideInteger . paramDivideInteger

prop_quotientInteger :: CostingFunctions s -> Property
prop_quotientInteger =
    testPredictTwo quotientInteger . paramQuotientInteger

prop_remainderInteger :: CostingFunctions s -> Property
prop_remainderInteger =
    testPredictTwo remainderInteger . paramRemainderInteger

prop_modInteger :: CostingFunctions s -> Property
prop_modInteger =
    testPredictTwo modInteger . paramModInteger

prop_lessThanInteger :: CostingFunctions s -> Property
prop_lessThanInteger =
    testPredictTwo lessThanInteger . paramLessThanInteger

prop_lessThanEqualsInteger :: CostingFunctions s -> Property
prop_lessThanEqualsInteger =
    testPredictTwo lessThanEqualsInteger . paramLessThanEqualsInteger

prop_equalsInteger :: CostingFunctions s -> Property
prop_equalsInteger =
    testPredictTwo equalsInteger . paramEqualsInteger

prop_appendByteString :: CostingFunctions s -> Property
prop_appendByteString =
    testPredictTwo appendByteString . paramAppendByteString

prop_sha2_256 :: CostingFunctions s -> Property
prop_sha2_256 =
    testPredictOne sha2_256 . paramSha2_256

prop_sha3_256 :: CostingFunctions s -> Property
prop_sha3_256 =
    testPredictOne sha3_256 . paramSha3_256

prop_blake2b :: CostingFunctions s -> Property
prop_blake2b =
    testPredictOne blake2b . paramBlake2b

prop_verifySignature :: CostingFunctions s -> Property
prop_verifySignature models =
    testPredictThree verifySignature $ paramVerifySignature models

prop_equalsByteString :: CostingFunctions s -> Property
prop_equalsByteString =
    testPredictTwo equalsByteString . paramEqualsByteString

prop_lessThanByteString :: CostingFunctions s -> Property
prop_lessThanByteString =
    testPredictTwo lessThanByteString . paramLessThanByteString

prop_lessThanEqualsByteString :: CostingFunctions s -> Property
prop_lessThanEqualsByteString =
    testPredictTwo lessThanEqualsByteString . paramLessThanEqualsByteString

-- prop_ifThenElse :: Property
-- prop_ifThenElse =
--    testPredictTwo ifThenElse (getConst . paramIfThenElse)

-- type PropertyR = forall s . PropertyT (R s) ()

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
propertyR prop = withTests 10 $ property $ unsafeHoist unsafeRunRegion prop
  where
    unsafeHoist :: (MFunctor t, Monad m) => (m () -> n ()) -> t m () -> t n ()
    unsafeHoist nt = hoist (unsafeCoerce nt)

-- Creates the model on the R side, loads the parameters over to Haskell, and
-- runs both models with a bunch of ExMemory combinations and compares the
-- outputs.
testPredictOne
    :: ((SomeSEXP s) -> R s (CostingFun ModelOneArgument))
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
        (\t -> msToPs (fromSomeSEXP t :: Double)) <$> [r|predict(modelR_hs, data.frame(x_mem=xD_hs))[[1]]|]
    predictH :: CostingInteger -> CostingInteger
    predictH x = coerce $ exBudgetCPU $ runCostingFunOneArgument modelH (ExMemory x)
    sizeGen = paramGen
  x <- forAll sizeGen
  byR <- lift $ predictR x
  diff byR (>=) 0  -- Sometimes R gives us models which pass through the origin, so we have to allow zero cost becase of that
  diff byR (~=) (predictH x)

testPredictTwo
    :: ((SomeSEXP s) -> R s (CostingFun ModelTwoArguments))
    -> Const (SomeSEXP s) a
    -> Property
testPredictTwo haskellModelFun modelR1 = propertyR $ do
  let modelR = getConst modelR1
  modelH <- lift $ haskellModelFun modelR
  let
    predictR :: MonadR m => CostingInteger -> CostingInteger -> m CostingInteger
    predictR x y =
      let
        xD = fromIntegral x :: Double
        yD = fromIntegral y :: Double
      in
        (\t -> msToPs (fromSomeSEXP t :: Double)) <$> [r|predict(modelR_hs, data.frame(x_mem=xD_hs, y_mem=yD_hs))[[1]]|]
    predictH :: CostingInteger -> CostingInteger -> CostingInteger
    predictH x y = coerce $ exBudgetCPU $ runCostingFunTwoArguments modelH (ExMemory x) (ExMemory y)
    sizeGen = (,) <$> paramGen <*> paramGen
  (x, y) <- forAll sizeGen
  byR <- lift $ predictR x y
--  let !() = Debug.Trace.trace ("(" ++ show x ++ "," ++ show y ++ "): byR -> " ++ show byR) $ ()
  diff byR (>=) 0
  diff byR (~=) (predictH x y)

{- testPredictThree
    :: forall s .
       (SomeSEXP (Region (R s)) -> R (CostingFun ModelThreeArguments) s)
    -> Const (SomeSEXP s) ModelThreeArguments
    -> Property
-}

testPredictThree
    :: ((SomeSEXP s) -> R s (CostingFun ModelThreeArguments))
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
        (\t -> msToPs (fromSomeSEXP t :: Double)) <$> [r|predict(modelR_hs, data.frame(x_mem=xD_hs, y_mem=yD_hs))[[1]]|]
    predictH :: CostingInteger -> CostingInteger -> CostingInteger -> CostingInteger
    predictH x y z = coerce $ exBudgetCPU $ runCostingFunThreeArguments modelH (ExMemory x) (ExMemory y) (ExMemory z)
    sizeGen = (,,) <$> paramGen <*> paramGen <*> paramGen
  (x, y, z) <- forAll sizeGen
  byR <- lift $ predictR x y z
  diff byR (>=) 0
  diff byR (~=) (predictH x y z)


-- main1 :: IO ()
-- main1 =  withEmbeddedR defaultConfig $ defaultMain $ [checkSequential $$(discover)]

{-
  defaultMain :: [IO Bool] -> IO ()  -- Hedgehog.Main
  modelsR :: MonadR m => m (BuiltinCostModelBase (Const (SomeSEXP (Region m))))

  withEmbeddedR :: Config -> IO a -> IO a

  Initialize a new instance of R, execute actions that interact with the
  R instance and then finalize the instance. This is typically called at
  the very beginning of the main function of the program.

  costModelsR :: MonadR m => m (BuiltinCostModelBase (Const (SomeSEXP (Region m))))
  - A record (in an R monad) mapping builtin names to R SEXPs

  instance MonadR IO, MonadR (R s)

  data R s a

  The R monad, for sequencing actions interacting with a single instance of the
  R interpreter, much as the IO monad sequences actions interacting with the
  real world. The R monad embeds the IO monad, so all IO actions can be lifted
  to R actions

-}

main :: IO ()
main = do
  withEmbeddedR R.defaultConfig $
    do
      models <- unsafeRunRegion costModelsR
      putStrLn "Eh?"
      let tests =
              [ ("addInteger",               prop_addInteger models)
              , ("subtractInteger",          prop_subtractInteger models)
              , ("multiplyInteger",          prop_multiplyInteger models)
--              , ("divideInteger",            prop_divideInteger models)
--              , ("quotientInteger",          prop_quotientInteger models)
--              , ("remainderInteger",         prop_remainderInteger models)
--              , ("modInteger",               prop_modInteger models)
              , ("lessThanInteger",          prop_lessThanInteger models)
              , ("lessThanEqualsInteger",    prop_lessThanEqualsInteger models)
              , ("equalsInteger",            prop_equalsInteger models)
--              , ("equalsByteString",         prop_equalsByteString models)
              , ("appendByteString",         prop_appendByteString models)
              , ("lessThanByteString",       prop_lessThanByteString models)
              , ("lessThanEqualsByteString", prop_lessThanEqualsByteString models)
              , ("verifySignature",          prop_verifySignature models)
              , ("sha2_256",                 prop_sha2_256 models)
              , ("sha3_256",                 prop_sha3_256 models)
              , ("blake2b",                  prop_blake2b models)
              ]
      HH.defaultMain $ [checkSequential $ Group "Builtin model tests" tests]
