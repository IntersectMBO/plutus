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
import           Control.DeepSeq
import           Control.Monad.Morph
import           CostModelCreation
import           Data.Coerce
import           Data.Functor.Compose
import           Foreign.R                                          hiding (unsafeCoerce)
import           GHC.Generics                                       (Generic, Generic1)
import           H.Prelude                                          (MonadR, Region, r)
import           Hedgehog
import qualified Hedgehog.Gen                                       as Gen
import           Hedgehog.Main
import qualified Hedgehog.Range                                     as Range
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.R                                         hiding (unsafeCoerce)
import           Unsafe.Coerce                                      (unsafeCoerce)


prop_addInteger = testPredict addInteger (getConst . paramAddInteger)
prop_subtractInteger = testPredict subtractInteger (getConst . paramSubtractInteger)
prop_multiplyInteger = testPredict multiplyInteger (getConst . paramMultiplyInteger)
prop_divideInteger = testPredict divideInteger (getConst . paramDivideInteger)
prop_quotientInteger = testPredict quotientInteger (getConst . paramQuotientInteger)
prop_remainderInteger = testPredict remainderInteger (getConst . paramRemainderInteger)
prop_modInteger = testPredict modInteger (getConst . paramModInteger)
prop_lessThanInteger = testPredict lessThanInteger (getConst . paramLessThanInteger)
prop_greaterThanInteger = testPredict greaterThanInteger (getConst . paramGreaterThanInteger)
prop_lessThanEqInteger = testPredict lessThanEqInteger (getConst . paramLessThanEqInteger)
prop_greaterThanEqInteger = testPredict greaterThanEqInteger (getConst . paramGreaterThanEqInteger)
prop_eqInteger = testPredict eqInteger (getConst . paramEqInteger)
  -- testPredict concatenate "concatenateModel"
  -- testPredict takeByteString "takeByteStringModel"
  -- testPredict dropByteString "dropByteStringModel"
  -- testPredict sHA2 "sha2Model"
  -- testPredict sHA3 "sha3Model"
  -- testPredict verifySignature "verifySignatureModel"
  -- testPredict eqByteString "eqByteStringModel"
  -- testPredict ltByteString "ltByteStringModel"
  -- testPredict gtByteString "gtByteStringModel"
  -- testPredict ifThenElse "ifThenElseModel"

probablySafeHoist :: (MFunctor t, Monad m) => (m () -> n ()) -> t m () -> t n ()
probablySafeHoist nt = hoist (unsafeCoerce nt)

testPredict :: forall s. ((SomeSEXP (Region (R s))) -> (R s) (CostingFun ModelTwoArguments))
  -> ((CostModelBase (Const (SomeSEXP (Region (R s))))) -> SomeSEXP s)
  -> Property
testPredict haskellModelFun modelFun = property $ probablySafeHoist unsafeRunRegion $ do
  modelR <- lift $ costModelR
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

main :: IO ()
main =  withEmbeddedR defaultConfig $ defaultMain $ [checkSequential $$(discover)]
