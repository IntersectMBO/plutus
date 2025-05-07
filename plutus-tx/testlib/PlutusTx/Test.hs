{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
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
  goldenPirReadableU,
  goldenPirBy,
  goldenTPlc,
  goldenUPlc,
  goldenUPlcReadable,

  -- * Evaluation testing
  goldenEvalCek,
  goldenEvalCekCatch,
  goldenEvalCekLog,

  -- * Budget and size testing
  goldenBudget,

  -- * Combined testing
  goldenBundle,
  goldenBundle'
) where

import Prelude

import Control.Exception (SomeException (..))
import Control.Lens (Field1 (_1))
import Control.Monad.Except (ExceptT, MonadError (throwError), runExceptT)
import Data.Either.Extras (fromRightM)
import Data.Kind (Type)
import Data.Tagged (Tagged (Tagged))
import Data.Text (Text)
import Flat (Flat)
import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Pretty (PrettyConfigClassic, PrettyConfigName, PrettyConst, PrettyUni,
                          prettyClassicSimple, prettyPlcClassicSimple, prettyReadable,
                          prettyReadableSimple)
import PlutusCore.Pretty qualified as PLC
import PlutusCore.Test (TestNested, ToTPlc (..), ToUPlc (..), catchAll, goldenSize, goldenTPlc,
                        goldenUPlc, goldenUPlcReadable, nestedGoldenVsDoc, nestedGoldenVsDocM,
                        ppCatch, rethrow, runUPlcBudget)
import PlutusIR.Analysis.Builtins qualified as PIR
import PlutusIR.Core.Type (progTerm)
import PlutusIR.Test ()
import PlutusIR.Transform.RewriteRules as PIR
import PlutusPrelude
import PlutusTx.Code (CompiledCode, CompiledCodeIn, getPir, getPirNoAnn, getPlcNoAnn, sizePlc)
import Test.Tasty (TestName, TestTree)
import Test.Tasty.Extras ()
import Test.Tasty.Providers (IsTest (run, testOptions), singleTest, testFailed, testPassed)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

-- `PlutusCore.Size` comparison tests

fitsUnder ::
  forall (a :: Type).
  (Typeable a) =>
  TestName ->
  (String, CompiledCode a) ->
  (String, CompiledCode a) ->
  TestTree
fitsUnder name test target = singleTest name $ SizeComparisonTest test target

data SizeComparisonTest (a :: Type)
  = SizeComparisonTest (TestName, CompiledCode a) (TestName, CompiledCode a)

instance (Typeable a) => IsTest (SizeComparisonTest a) where
  run _ (SizeComparisonTest (mName, mCode) (tName, tCode)) _ = do
    let tEstimate = sizePlc tCode
    let mEstimate = sizePlc mCode
    let diff = tEstimate - mEstimate
    pure $ case signum diff of
      (-1) ->
        testFailed $ renderFailed (tName, tEstimate) (mName, mEstimate) diff
      0 ->
        testPassed $ renderEstimates (tName, tEstimate) (mName, mEstimate)
      _ ->
        testPassed $ renderExcess (tName, tEstimate) (mName, mEstimate) diff
  testOptions = Tagged []

renderFailed :: (TestName, Integer) -> (TestName, Integer) -> Integer -> String
renderFailed tData mData diff =
  renderEstimates tData mData <> "Exceeded by: " <> show diff

renderEstimates :: (TestName, Integer) -> (TestName, Integer) -> String
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

renderExcess :: (TestName, Integer) -> (TestName, Integer) -> Integer -> String
renderExcess tData mData diff =
  renderEstimates tData mData <> "Remaining headroom: " <> show diff

goldenBudget :: TestName -> CompiledCode a -> TestNested
goldenBudget name compiledCode = do
  nestedGoldenVsDocM name ".budget" $ ppCatch $ do
    PLC.ExBudget cpu mem <- runUPlcBudget [compiledCode]
    size <- UPLC.programSize <$> toUPlc compiledCode
    let contents =
          "cpu: "
            <> pretty cpu
            <> "\nmem: "
            <> pretty mem
            <> "\nsize: "
            <> pretty size
    pure (render @Text contents)

goldenBundle
  :: TestName
  -> CompiledCodeIn UPLC.DefaultUni UPLC.DefaultFun a
  -> CompiledCodeIn UPLC.DefaultUni UPLC.DefaultFun b
  -> TestNested
goldenBundle name x y = do
  goldenPirReadable name x
  goldenUPlcReadable name x
  goldenEvalCekCatch name [y]
  goldenBudget name y

goldenBundle'
  :: TestName
  -> CompiledCodeIn UPLC.DefaultUni UPLC.DefaultFun a
  -> TestNested
goldenBundle' name x = goldenBundle name x x

-- Compilation testing

-- | Does not print uniques.
goldenPir ::
  (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun) =>
  TestName ->
  CompiledCodeIn uni fun a ->
  TestNested
goldenPir name value =
  nestedGoldenVsDoc name ".pir"
    . maybe
      "PIR not found in CompiledCode"
      (prettyClassicSimple . view progTerm)
    $ getPirNoAnn value

-- | Does not print uniques.
goldenPirReadable ::
  (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun) =>
  TestName ->
  CompiledCodeIn uni fun a ->
  TestNested
goldenPirReadable name value =
  nestedGoldenVsDoc name ".pir"
    . maybe
      "PIR not found in CompiledCode"
      (prettyReadableSimple . view progTerm)
    $ getPirNoAnn value

-- | Prints uniques. This should be used sparingly: a simple change to a script or a
-- compiler pass may change all uniques, making it difficult to see the actual
-- change if all uniques are printed. It is nonetheless useful sometimes.
goldenPirReadableU ::
  (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun) =>
  TestName ->
  CompiledCodeIn uni fun a ->
  TestNested
goldenPirReadableU name value =
  nestedGoldenVsDoc name ".pir"
    . maybe "PIR not found in CompiledCode" (prettyReadable . view progTerm)
    $ getPirNoAnn value

goldenPirBy ::
  (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun) =>
  PrettyConfigClassic PrettyConfigName ->
  TestName ->
  CompiledCodeIn uni fun a ->
  TestNested
goldenPirBy config name value =
  nestedGoldenVsDoc name ".pir" $ prettyBy config $ getPir value

-- Evaluation testing

-- TODO: rationalize with the functions exported from PlcTestUtils
goldenEvalCek :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun) => TestName -> [a] -> TestNested
goldenEvalCek name values =
  nestedGoldenVsDocM name ".eval" $
    prettyPlcClassicSimple <$> rethrow (runPlcCek values)

goldenEvalCekCatch :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun) => TestName -> [a] -> TestNested
goldenEvalCekCatch name values =
  nestedGoldenVsDocM name ".eval" $
    either (pretty . show) prettyPlcClassicSimple
      <$> runExceptT (runPlcCek values)

goldenEvalCekLog :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun) => TestName -> [a] -> TestNested
goldenEvalCekLog name values =
  nestedGoldenVsDocM name ".eval" $
    prettyPlcClassicSimple . view _1 <$> (rethrow $ runPlcCekTrace values)

-- Helpers

instance
  (PLC.Closed uni, uni `PLC.Everywhere` Flat, Flat fun)
  => ToUPlc (CompiledCodeIn uni fun a) uni fun
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
  , Default (PIR.BuiltinsInfo uni fun)
  , Default (PIR.RewriteRules uni fun)
  )
  => ToTPlc (CompiledCodeIn uni fun a) uni fun
  where
  toTPlc v = do
    mayV' <- catchAll $ getPir v
    case mayV' of
      Nothing -> fail "No PIR available"
      Just v' -> toTPlc v'

runPlcCek
  :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun)
  => [a]
  -> ExceptT
       SomeException
       IO
       (UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ())
runPlcCek values = do
  ps <- traverse toUPlc values
  let p = foldl1 (unsafeFromRight .* UPLC.applyProgram) ps
  fromRightM (throwError . SomeException) $
    UPLC.evaluateCekNoEmit
      PLC.defaultCekParametersForTesting
      (p ^. UPLC.progTerm)

runPlcCekTrace
  :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun)
  => [a]
  -> ExceptT
       SomeException
       IO
       ( [Text]
       , UPLC.CekExTally PLC.DefaultFun
       , UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ()
       )
runPlcCekTrace values = do
  ps <- traverse toUPlc values
  let p = foldl1 (unsafeFromRight .* UPLC.applyProgram) ps
  let (result, UPLC.TallyingSt tally _, logOut) =
        UPLC.runCek
          PLC.defaultCekParametersForTesting
          UPLC.tallying
          UPLC.logEmitter
          (p ^. UPLC.progTerm)
  res <- fromRightM (throwError . SomeException) result
  pure (logOut, tally, res)
