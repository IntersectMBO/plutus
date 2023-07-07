-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

import PlutusCore.DataFilePaths qualified as DFP
import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetStream (sumExBudgetStream)
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Machine.ExMemoryUsage

import CreateBuiltinCostModel
import TH

import Control.Applicative (Const, getConst)
import Control.Monad.Morph (MFunctor, hoist, lift)
import Data.Coerce (coerce)
import Data.SatInt
import Data.String (fromString)
import Unsafe.Coerce (unsafeCoerce)

import H.Prelude as H (MonadR, io)
import Language.R as R (R, SomeSEXP, defaultConfig, fromSomeSEXP, runRegion, unsafeRunRegion,
                        withEmbeddedR)
import Language.R.QQ (r)

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Main qualified as HH (defaultMain)
import Hedgehog.Range qualified as Range

{- | This module is supposed to test that the R cost models for built-in functions
   defined in models.R (using the CSV output from 'cost-model-budgeting-bench'))
   produce the same results as the Haskell versions. However there are a couple
   of subtleties.  (A) The R models use floating point numbers and the Haskell
   versions use CostingIntegers, and there will be some difference in precision
   because of this. (B) The R models produce results in microseconds and the
   Haskell versions produce results in picoseconds. We deal with (B) by using
   the microToPico function from CreateBuiltinCostModel to convert R results to
   picoseconds expressed as CostingIntegers.  To deal with (A), we don't check
   for exact equality of the outputs but instead check that the R result and the
   Haskell result agreee to within a factor of 1/100 (one percent).
-}

-- | Maximum allowable difference beween R result and Haskell result.
epsilon :: Double
epsilon = 1/100

{-
   The tests here use Haskell costing functions (in 'costModelsR' from
   'CreateBuiltinCostModel.hs') which are loaded directly from R, based purely
   on the contents of benching.csv, which must be present in
   plutus-core/cost-model/data.  The costing functions we use in practice are
   read from 'builtinCostModel.json', which contains JSON-serialised versions of
   the Haskell costing functions.  Perhaps the tests should be reading the
   Haskell costing functions from the JSON file as well; there shouldn't really
   be any problem because the functions should be the same as the ones we
   construct from R here (they're essentially the contents of 'costModelsR'
   converted to JSON), but it wouldn't do any harm to include any possible loss
   of accuracy due to serialisation/deserialisation in the tests as well.  Doing
   the tests the way they're done here is arguably better because it may reveal
   problems in the costing interface before the cost model file is updated, and
   we want to be sure that we don’t include an incorrect costing function in the
   JSON. Maybe it would be sensible to have some separate tests that check that
   converting to JSON and then back is the identity.
-}

-- How many tests to run for each costing function
numberOfTests :: TestLimit
numberOfTests = 100

-- | Generate inputs for costing functions, making sure that we test a large
-- range of inputs, but that we also get small inputs.
memUsageGen :: Gen CostingInteger
memUsageGen =
    Gen.choice [small, large]
        where small = unsafeToSatInt <$> Gen.integral (Range.constant 0 2)
              large = unsafeToSatInt <$> Gen.integral (Range.linear 0 5000)

-- A type alias to make our signatures more concise.  This type is a record in
-- which every field refers to an R SEXP (over some state s), the lm model for
-- the benchmark data for the relevant builtin.
type RModels s = BuiltinCostModelBase (Const (SomeSEXP s))

{- The region in the plane where we want to carry out tests for a two-dimensional
   model.  The Haskell versions of some of these models are defined in several
   pieces and we don't yet have corresponding piecewise R models, so we just
   restrict to the places where the piecewise models are interesting (they're
   typically constant elsewhere). -}
data TestDomain
  = Everywhere
  | OnDiagonal
  | BelowDiagonal

-- Approximate equality
(~=) :: CostingInteger -> CostingInteger -> Bool
x ~= y
  | x==0 && y==0 = True
  | otherwise = err < epsilon
    where x' = fromSatInt x :: Double
          y' = fromSatInt y :: Double
          err = abs ((x'-y')/y')

-- Runs property tests in the `R` Monad.
propertyR :: PropertyT (R s) () -> Property
{- Why all the unsafe, you ask? `runRegion` (from inline-r) has a `(forall s. R s
   a)` to ensure no `R` types leave the scope. Additionally, it has an `NFData`
   constraint to ensure no unexecuted R code escapes. `unsafeRunRegion` does
   away with the first constraint. However, conjuring up a `NFData` constraint
   for `PropertyT` is impossible, because internally, `PropertyT` constructs a
   `TreeT` to hold all the branches for reduction. These branches will contain
   `(R s)`, which has a `MonadIO` instance. No `NFData` for `IO`, so no `NFData`
   for `TreeT`. For now, this didn't crash yet.

   Update: running the tests thousands of times, they did hang once or twice and
   there were very occasional errors like "Error in `[.tbl_df`(x_in, vars$x$out)
   : 'rho' must be an environment not promise: detected in C-level eval" and
   "Error: attempt to apply non-function".  Also, if you try 'checkParallel'
   instead of 'checkSequential' you very quickly get an error beginning "stack
   imbalance in 'lazyLoadDBfetch". These errors are coming from R, but it's not
   clear whether they're due to this code or to some problem elsewhere, and it's
   not easy to test.  This code isn't critical, so we can get away with
   occasional failures.  It's probably best not to have the tests enabled in CI
   though and just run them manually when required.
-}
propertyR prop = withTests numberOfTests $ property $ unsafeHoist unsafeRunRegion prop
  where
    unsafeHoist :: (MFunctor t, Monad m) => (m () -> n ()) -> t m () -> t n ()
    unsafeHoist nt = hoist (unsafeCoerce nt)

{- The runCostingFun<N>Arguments functions take objects as arguments, calculate
   the size measures (memoryUsage) of those objects, and then apply the actual
   costing functions to those sizes.  Here we want to feed sizes directly to the
   costing functions (no intermediate objects), so given a size n we wrap it the
   type below which has an ExMemoryUsage instance which returns n, _not_ the
   size of n (which would usually be 1).  This type should not be used outside
   this module because the memoryUsage function doesn't accurately reflect
   sizes.
-}
newtype ExM = ExM CostingInteger
instance ExMemoryUsage ExM where
    memoryUsage (ExM n) = singletonRose n

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
            xD = fromSatInt x :: Double
        in
          microToPico . fromSomeSEXP <$> [r|predict(modelR_hs, data.frame(x_mem=xD_hs))[[1]]|]
    predictH :: CostingInteger -> CostingInteger
    predictH x =
      coerce $ exBudgetCPU $ sumExBudgetStream $
        runCostingFunOneArgument modelH (ExM x)
    sizeGen = memUsageGen
  x <- forAll sizeGen
  byR <- lift $ predictR x
  -- Sometimes R gives us models which pass through the origin, so we have to allow zero cost
  -- because of that
  diff byR (>=) 0
  diff byR (~=) (predictH x)

testPredictTwo
    :: forall s a .
       (SomeSEXP s -> R s (CostingFun ModelTwoArguments))
    -> Const (SomeSEXP s) a
    -> TestDomain
    -> Property
testPredictTwo haskellModelFun modelR1 domain = propertyR $ do
  let modelR = getConst modelR1
  modelH <- lift $ haskellModelFun modelR
  let
    predictR :: MonadR m => CostingInteger -> CostingInteger -> m CostingInteger
    predictR x y =
      let
        xD = fromSatInt x :: Double
        yD = fromSatInt y :: Double
      in
        microToPico . fromSomeSEXP <$>
          [r|predict(modelR_hs, data.frame(x_mem=xD_hs, y_mem=yD_hs))[[1]]|]
    predictH :: CostingInteger -> CostingInteger -> CostingInteger
    predictH x y =
      coerce $ exBudgetCPU $ sumExBudgetStream $
        runCostingFunTwoArguments modelH (ExM x) (ExM y)
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
    predictR x y z =
      let
        xD = fromSatInt x :: Double
        yD = fromSatInt y :: Double
        zD = fromSatInt z :: Double
      in
        microToPico . fromSomeSEXP <$>
          [r|predict(modelR_hs, data.frame(x_mem=xD_hs, y_mem=yD_hs, z_mem=zD_hs))[[1]]|]
    predictH :: CostingInteger -> CostingInteger -> CostingInteger -> CostingInteger
    predictH x y z =
      coerce $ exBudgetCPU $ sumExBudgetStream $
        runCostingFunThreeArguments modelH (ExM x) (ExM y) (ExM z)
    sizeGen = (,,) <$> memUsageGen <*> memUsageGen <*> memUsageGen
  (x, y, z) <- forAll sizeGen
  byR <- lift $ predictR x y z
  diff byR (>=) 0
  diff byR (~=) (predictH x y z)


testPredictSix
    :: (SomeSEXP s -> R s (CostingFun ModelSixArguments))
    -> Const (SomeSEXP s) a
    -> Property
testPredictSix haskellModelFun modelR1 = propertyR $ do
  let modelR = getConst modelR1
  modelH <- lift $ haskellModelFun modelR
  let
    predictR :: MonadR m => CostingInteger -> CostingInteger -> CostingInteger
             -> CostingInteger -> CostingInteger -> CostingInteger -> m CostingInteger
    predictR x y z u v  w =
      let
        xD = fromSatInt x :: Double
        yD = fromSatInt y :: Double
        zD = fromSatInt z :: Double
        uD = fromSatInt u :: Double
        vD = fromSatInt v :: Double
        wD = fromSatInt w :: Double
      in
        microToPico . fromSomeSEXP <$>
          [r|predict(modelR_hs, data.frame(x_mem=xD_hs, y_mem=yD_hs, z_mem=zD_hs,
                                          u_mem=uD_hs, v_mem=vD_hs, w_mem=wD_hs))[[1]]|]
    predictH :: CostingInteger
      -> CostingInteger
      -> CostingInteger
      -> CostingInteger
      -> CostingInteger
      -> CostingInteger
      -> CostingInteger
    predictH x y z u v w =
      coerce $ exBudgetCPU $ sumExBudgetStream $
        runCostingFunSixArguments modelH (ExM x) (ExM y) (ExM z) (ExM u) (ExM v) (ExM w)
    sizeGen =
      (,,,,,) <$> memUsageGen <*> memUsageGen <*> memUsageGen <*> memUsageGen <*> memUsageGen
        <*> memUsageGen
  (x, y, z, u, v, w) <- forAll sizeGen
  byR <- lift $ predictR x y z u v w
  diff byR (>=) 0
  diff byR (~=) (predictH x y z u v w)


makeProp1
    :: String
    -> (SomeSEXP s -> R s (CostingFun ModelOneArgument))
    -> (RModels s -> Const (SomeSEXP s) b)
    -> RModels s
    -> (PropertyName, Property)
makeProp1 name fun param models =
    (fromString name, testPredictOne fun (param models))

makeProp2
    :: String
    -> (SomeSEXP s -> R s (CostingFun ModelTwoArguments))
    -> (RModels s -> Const (SomeSEXP s) b)
    -> RModels s
    -> TestDomain
    -> (PropertyName, Property)
makeProp2 name fun param models domain =
    (fromString name, testPredictTwo fun (param models) domain)

makeProp3
    :: String
    -> (SomeSEXP s -> R s (CostingFun ModelThreeArguments))
    -> (RModels s -> Const (SomeSEXP s) b)
    -> RModels s
    -> (PropertyName, Property)
makeProp3 name fun param models =
    (fromString name, testPredictThree fun (param models))

makeProp6
    :: String
    -> (SomeSEXP s -> R s (CostingFun ModelSixArguments))
    -> (RModels s -> Const (SomeSEXP s) b)
    -> RModels s
    -> (PropertyName, Property)
makeProp6 name fun param models =
    (fromString name, testPredictSix fun (param models))

main :: IO ()
main =
    withEmbeddedR R.defaultConfig $ runRegion $ do
      models <- CreateBuiltinCostModel.costModelsR DFP.benchingResultsFile DFP.rModelFile
      H.io $ HH.defaultMain [checkSequential $ Group "Costing function tests" (tests models)]
          where tests models =
            -- 'models' doesn't appear explicitly below, but 'genTest' generates code which uses it.
                    [ $(genTest 2 "addInteger")            Everywhere
                    , $(genTest 2 "subtractInteger")       Everywhere
                    , $(genTest 2 "multiplyInteger")       Everywhere
                    , $(genTest 2 "divideInteger")         BelowDiagonal
                    , $(genTest 2 "quotientInteger")       BelowDiagonal
                    , $(genTest 2 "remainderInteger")      BelowDiagonal
                    , $(genTest 2 "modInteger")            BelowDiagonal
                    , $(genTest 2 "lessThanInteger")       Everywhere
                    , $(genTest 2 "lessThanEqualsInteger") Everywhere
                    , $(genTest 2 "equalsInteger")         Everywhere

                    -- Bytestrings
                    , $(genTest 2 "appendByteString")         Everywhere
                    , $(genTest 2 "consByteString")           Everywhere
                    , $(genTest 3 "sliceByteString")
                    , $(genTest 1 "lengthOfByteString")
                    , $(genTest 2 "indexByteString")          Everywhere
                    , $(genTest 2 "equalsByteString")         OnDiagonal
                    , $(genTest 2 "lessThanByteString")       Everywhere
                    , $(genTest 2 "lessThanEqualsByteString") Everywhere

                    -- Cryptography and hashes
                    , $(genTest 1 "sha2_256")
                    , $(genTest 1 "sha3_256")
                    , $(genTest 1 "blake2b_256")
                    -- , $(genTest 3 "verifyEd25519Signature")
                    -- ^ Disabled for the time being: see the comment in CreateBuiltinCostModel.hs
                    , $(genTest 3 "verifyEcdsaSecp256k1Signature")
                    , $(genTest 3 "verifySchnorrSecp256k1Signature")

                    -- Strings
                    , $(genTest 2 "appendString") Everywhere
                    , $(genTest 2 "equalsString") OnDiagonal
                    , $(genTest 1 "encodeUtf8")
                    , $(genTest 1 "decodeUtf8")

                    -- Bool
                    , $(genTest 3 "ifThenElse")

                    -- Unit
                    , $(genTest 2 "chooseUnit") Everywhere

                    -- Tracing
                    , $(genTest 2 "trace") Everywhere

                    -- Pairs
                    , $(genTest 1 "fstPair")
                    , $(genTest 1 "sndPair")

                    -- Lists
                    , $(genTest 3 "chooseList")
                    , $(genTest 2 "mkCons") Everywhere
                    , $(genTest 1 "headList")
                    , $(genTest 1 "tailList")
                    , $(genTest 1 "nullList")

                    -- Data
                    , $(genTest 6 "chooseData")
                    , $(genTest 2 "constrData") Everywhere
                    , $(genTest 1 "mapData")
                    , $(genTest 1 "listData")
                    , $(genTest 1 "iData")
                    , $(genTest 1 "bData")
                    , $(genTest 1 "unConstrData")
                    , $(genTest 1 "unMapData")
                    , $(genTest 1 "unListData")
                    , $(genTest 1 "unIData")
                    , $(genTest 1 "unBData")
                    , $(genTest 2 "equalsData") Everywhere
                    , $(genTest 1 "serialiseData")

                    -- Misc constructors
                    , $(genTest 2 "mkPairData") Everywhere
                    , $(genTest 1 "mkNilData")
                    , $(genTest 1 "mkNilPairData")

                    -- BLS
                    , $(genTest 2 "bls12_381_G1_add")         Everywhere
                    , $(genTest 1 "bls12_381_G1_neg")
                    , $(genTest 2 "bls12_381_G1_scalarMul")   Everywhere
                    , $(genTest 2 "bls12_381_G1_equal")       Everywhere
                    , $(genTest 1 "bls12_381_G1_compress")
                    , $(genTest 1 "bls12_381_G1_uncompress")
                    , $(genTest 2 "bls12_381_G1_hashToGroup") Everywhere
                    , $(genTest 2 "bls12_381_G2_add")         Everywhere
                    , $(genTest 1 "bls12_381_G2_neg")
                    , $(genTest 2 "bls12_381_G2_scalarMul")   Everywhere
                    , $(genTest 2 "bls12_381_G2_equal")       Everywhere
                    , $(genTest 1 "bls12_381_G2_compress")
                    , $(genTest 1 "bls12_381_G2_uncompress")
                    , $(genTest 2 "bls12_381_G2_hashToGroup") Everywhere
                    , $(genTest 2 "bls12_381_millerLoop")     Everywhere
                    , $(genTest 2 "bls12_381_mulMlResult")    Everywhere
                    , $(genTest 2 "bls12_381_finalVerify")    Everywhere

                    -- Keccak_256, Blake2b_224
                    , $(genTest 1 "keccak_256")
                    , $(genTest 1 "blake2b_224")
                   ]

