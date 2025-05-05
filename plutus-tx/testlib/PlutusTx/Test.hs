{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module PlutusTx.Test (
  -- * Compilation testing
  goldenPir,
  goldenPirReadable,
  goldenPirReadableU,
  goldenPirBy,
  goldenTPlc,
  goldenUPlc,
  goldenUPlcReadable,
  goldenBudget,
  goldenSize,

  -- * Evaluation for testing
  runPlcCek,
  runPlcCekTrace,

  -- * Golden evaluation testing
  goldenEvalCek,
  goldenEvalCekLog,
  goldenEvalCekCatchBudget,

  -- * Combined testing
  goldenBundle,
  goldenBundle',
) where

import Prelude

import Control.Exception (SomeException (..))
import Control.Lens (Field1 (_1), view, (^.))
import Control.Monad.Except (ExceptT, MonadError (throwError))
import Data.Either.Extras (fromRightM)
import Data.Text (Text)
import Flat (Flat)
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Pretty (Pretty, PrettyConfigClassic, PrettyConfigName, PrettyUni, pretty,
                          prettyBy, prettyClassicSimple, prettyPlcClassicSimple, prettyReadable,
                          prettyReadableSimple, render)
import PlutusCore.Test (TestNested, ToUPlc (..), goldenSize, goldenTPlc, goldenUPlc,
                        goldenUPlcReadable, nestedGoldenVsDoc, nestedGoldenVsDocM, ppCatch, rethrow,
                        runUPlcBudget)
import PlutusIR.Core.Type (progTerm)
import PlutusIR.Test ()
import PlutusTx.Code (CompiledCode, CompiledCodeIn, getPir, getPirNoAnn)
import PlutusTx.Test.Orphans ()
import Test.Tasty (TestName)
import Test.Tasty.Extras ()
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

--------------------------------------------------------------------------------
-- Evaluation for testing ------------------------------------------------------

runPlcCek
  :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun)
  => a
  -> ExceptT
       SomeException
       IO
       (UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ())
runPlcCek val = do
  term <- toUPlc val
  fromRightM (throwError . SomeException) $
    UPLC.evaluateCekNoEmit
      PLC.defaultCekParametersForTesting
      (term ^. UPLC.progTerm)

runPlcCekBudget
  :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun)
  => a
  -> ExceptT
       SomeException
       IO
       (UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun (), PLC.ExBudget)
runPlcCekBudget val = do
  term <- toUPlc val
  fromRightM (throwError . SomeException) $ do
    let
      (evalRes, UPLC.CountingSt budget) =
        UPLC.runCekNoEmit
          PLC.defaultCekParametersForTesting
          UPLC.counting
          (term ^. UPLC.progTerm)

    (,budget) <$> evalRes

runPlcCekTrace
  :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun)
  => a
  -> ExceptT
       SomeException
       IO
       ( [Text]
       , UPLC.CekExTally PLC.DefaultFun
       , UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ()
       )
runPlcCekTrace value = do
  term <- toUPlc value
  let (result, UPLC.TallyingSt tally _, logOut) =
        UPLC.runCek
          PLC.defaultCekParametersForTesting
          UPLC.tallying
          UPLC.logEmitter
          (term ^. UPLC.progTerm)
  res <- fromRightM (throwError . SomeException) result
  pure (logOut, tally, res)

--------------------------------------------------------------------------------
-- Evaluation for testing: golden files ----------------------------------------

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
  goldenEvalCekCatchBudget name y

goldenBundle'
  :: TestName
  -> CompiledCodeIn UPLC.DefaultUni UPLC.DefaultFun a
  -> TestNested
goldenBundle' name x = goldenBundle name x x

-- | Does not print uniques.
goldenPir
  :: (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun)
  => TestName
  -> CompiledCodeIn uni fun a
  -> TestNested
goldenPir name value =
  nestedGoldenVsDoc name ".pir"
    . maybe
      "PIR not found in CompiledCode"
      (prettyClassicSimple . view progTerm)
    $ getPirNoAnn value

-- | Does not print uniques.
goldenPirReadable
  :: (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun)
  => TestName
  -> CompiledCodeIn uni fun a
  -> TestNested
goldenPirReadable name value =
  nestedGoldenVsDoc name ".pir"
    . maybe
      "PIR not found in CompiledCode"
      (prettyReadableSimple . view progTerm)
    $ getPirNoAnn value

{-| Prints uniques. This should be used sparingly: a simple change to a script or a
compiler pass may change all uniques, making it difficult to see the actual
change if all uniques are printed. It is nonetheless useful sometimes.
-}
goldenPirReadableU
  :: (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun)
  => TestName
  -> CompiledCodeIn uni fun a
  -> TestNested
goldenPirReadableU name value =
  nestedGoldenVsDoc name ".pir"
    . maybe "PIR not found in CompiledCode" (prettyReadable . view progTerm)
    $ getPirNoAnn value

goldenPirBy
  :: (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun)
  => PrettyConfigClassic PrettyConfigName
  -> TestName
  -> CompiledCodeIn uni fun a
  -> TestNested
goldenPirBy config name value =
  nestedGoldenVsDoc name ".pir" $ prettyBy config $ getPir value

goldenEvalCek
  :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun)
  => TestName -> a -> TestNested
goldenEvalCek name term =
  nestedGoldenVsDocM name ".eval" $
    prettyPlcClassicSimple <$> rethrow (runPlcCek term)

goldenEvalCekLog
  :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun)
  => TestName -> a -> TestNested
goldenEvalCekLog name term =
  nestedGoldenVsDocM name ".eval" $
    prettyPlcClassicSimple . view _1 <$> rethrow (runPlcCekTrace term)

goldenEvalCekCatchBudget :: TestName -> CompiledCode a -> TestNested
goldenEvalCekCatchBudget name compiledCode =
  nestedGoldenVsDocM name ".eval" $ ppCatch $ do
    (termRes, PLC.ExBudget cpu mem) <- runPlcCekBudget compiledCode
    size <- UPLC.programSize <$> toUPlc compiledCode
    let contents =
          "cpu: "
            <> pretty cpu
            <> "\nmem: "
            <> pretty mem
            <> "\nsize: "
            <> pretty size
            <> "\n\n"
            <> prettyPlcClassicSimple termRes
    pure (render @Text contents)
