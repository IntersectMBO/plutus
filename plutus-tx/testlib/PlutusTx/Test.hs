{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusTx.Test (
  -- * Size tests
  goldenSize,
  fitsUnder,

  -- * Compilation testing
  goldenPir,
  goldenPirReadable,
  goldenPirBy,
  goldenTPlc,
  goldenUPlc,
  goldenUPlcReadable,

  -- * Evaluation testing
  goldenEvalCek,
  goldenEvalCekCatch,
  goldenEvalCekLog,

  -- * Budget testing
  goldenBudget

) where

import Prelude

import Control.Exception
import Control.Lens
import Control.Monad.Except
import Data.Either.Extras
import Data.Kind (Type)
import Data.Tagged (Tagged (Tagged))
import Data.Text (Text)
import Flat (Flat)
import Prettyprinter
import Test.Tasty (TestName, TestTree)
import Test.Tasty.Extras
import Test.Tasty.Providers (IsTest (run, testOptions), singleTest, testFailed, testPassed)

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Pretty
import PlutusCore.Pretty qualified as PLC
import PlutusCore.Test
import PlutusIR.Core.Type (progTerm)
import PlutusIR.Test ()
import PlutusPrelude
import PlutusTx.Code (CompiledCode, CompiledCodeIn, getPir, getPirNoAnn, getPlcNoAnn, sizePlc)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

-- `PlutusCore.Size` testing (golden tests)

goldenSize :: (PLC.Closed uni, Flat fun, PLC.Everywhere uni Flat) =>
  -- | The name of the test
  String ->
  -- | The input for checking the size
  CompiledCodeIn uni fun a ->
  TestNested
goldenSize name value =
  nestedGoldenVsDoc name ".uplc-size" (pretty $ sizePlc value)

-- `PlutusCore.Size` comparison tests

fitsUnder ::
  forall (a :: Type).
  (Typeable a) =>
  String ->
  (String, CompiledCode a) ->
  (String, CompiledCode a) ->
  TestTree
fitsUnder name test target = singleTest name $ SizeComparisonTest test target

data SizeComparisonTest (a :: Type)
  = SizeComparisonTest (String, CompiledCode a) (String, CompiledCode a)

instance (Typeable a) => IsTest (SizeComparisonTest a) where
  run _ (SizeComparisonTest (mName, mCode) (tName, tCode)) _ = do
    let tEstimate = sizePlc tCode
    let mEstimate = sizePlc mCode
    let diff = tEstimate - mEstimate
    pure $ case signum diff of
      (-1) -> testFailed . renderFailed (tName, tEstimate) (mName, mEstimate) $ diff
      0    -> testPassed . renderEstimates (tName, tEstimate) $ (mName, mEstimate)
      _    -> testPassed . renderExcess (tName, tEstimate) (mName, mEstimate) $ diff
  testOptions = Tagged []

renderFailed :: (String, Integer) -> (String, Integer) -> Integer -> String
renderFailed tData mData diff =
  renderEstimates tData mData
    <> "Exceeded by: "
    <> show diff

renderEstimates :: (String, Integer) -> (String, Integer) -> String
renderEstimates (tName, tEstimate) (mName, mEstimate) =
  "Target: "
    <> tName
    <> "; size "
    <> show tEstimate
    <> "\n"
    <> "Measured: "
    <> mName
    <> "; size "
    <> show mEstimate
    <> "\n"

renderExcess :: (String, Integer) -> (String, Integer) -> Integer -> String
renderExcess tData mData diff =
  renderEstimates tData mData
    <> "Remaining headroom: "
    <> show diff

-- Budget testing

goldenBudget :: TestName -> CompiledCode a -> TestNested
goldenBudget name compiledCode = goldenUplcBudget name (UPLC._progTerm (getPlcNoAnn compiledCode))

-- Compilation testing

goldenPir ::
  (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun) =>
  String ->
  CompiledCodeIn uni fun a ->
  TestNested
goldenPir name value = nestedGoldenVsDoc name ".pir" $ pretty $ getPirNoAnn value

-- | Does not print uniques.
goldenPirReadable ::
  (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun) =>
  String ->
  CompiledCodeIn uni fun a ->
  TestNested
goldenPirReadable name value =
  nestedGoldenVsDoc name ".pir-readable"
    . maybe "PIR not found in CompiledCode" (pretty . AsReadable . view progTerm)
    $ getPirNoAnn value

goldenPirBy ::
  (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun) =>
  PrettyConfigClassic PrettyConfigName ->
  String ->
  CompiledCodeIn uni fun a ->
  TestNested
goldenPirBy config name value =
  nestedGoldenVsDoc name ".pir" $
    pretty $
      AttachPrettyConfig config $
        getPir value

-- Evaluation testing

-- TODO: rationalize with the functions exported from PlcTestUtils
goldenEvalCek :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun) => String -> [a] -> TestNested
goldenEvalCek name values =
  nestedGoldenVsDocM name ".eval-cek" $ prettyPlcClassicDebug <$> (rethrow $ runPlcCek values)

goldenEvalCekCatch :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun) => String -> [a] -> TestNested
goldenEvalCekCatch name values =
  nestedGoldenVsDocM name ".eval-cek-catch" $
    either (pretty . show) prettyPlcClassicDebug <$> runExceptT (runPlcCek values)

goldenEvalCekLog :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun) => String -> [a] -> TestNested
goldenEvalCekLog name values =
  nestedGoldenVsDocM name ".eval-cek-log" $ pretty . view _1 <$> (rethrow $ runPlcCekTrace values)

-- Helpers

instance
  (PLC.Closed uni, uni `PLC.Everywhere` Flat, Flat fun) =>
  ToUPlc (CompiledCodeIn uni fun a) uni fun
  where
  toUPlc v = do
    v' <- catchAll $ getPlcNoAnn v
    toUPlc v'

instance
  ( PLC.PrettyParens (PLC.SomeTypeIn uni)
  , PLC.GEq uni
  , PLC.Typecheckable uni fun
  , PLC.Closed uni
  , uni `PLC.Everywhere` PrettyConst
  , Pretty fun
  , uni `PLC.Everywhere` Flat
  , Flat fun
  , Default (PLC.CostingPart uni fun)
  ) =>
  ToTPlc (CompiledCodeIn uni fun a) uni fun
  where
  toTPlc v = do
    mayV' <- catchAll $ getPir v
    case mayV' of
      Nothing -> fail "No PIR available"
      Just v' -> toTPlc v'

runPlcCek ::
  (ToUPlc a PLC.DefaultUni PLC.DefaultFun) =>
  [a] ->
  ExceptT SomeException IO (UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ())
runPlcCek values = do
  ps <- traverse toUPlc values
  let p =
        foldl1 (unsafeFromRight .* UPLC.applyProgram) ps
  fromRightM (throwError . SomeException) $
    UPLC.evaluateCekNoEmit PLC.defaultCekParameters (p ^. UPLC.progTerm)

runPlcCekTrace ::
  (ToUPlc a PLC.DefaultUni PLC.DefaultFun) =>
  [a] ->
  ExceptT
    SomeException
    IO
    ([Text], UPLC.CekExTally PLC.DefaultFun, UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ())
runPlcCekTrace values = do
  ps <- traverse toUPlc values
  let p =
        foldl1 (unsafeFromRight .* UPLC.applyProgram) ps
  let (result, UPLC.TallyingSt tally _, logOut) =
        UPLC.runCek PLC.defaultCekParameters UPLC.tallying UPLC.logEmitter (p ^. UPLC.progTerm)
  res <- fromRightM (throwError . SomeException) result
  pure (logOut, tally, res)
