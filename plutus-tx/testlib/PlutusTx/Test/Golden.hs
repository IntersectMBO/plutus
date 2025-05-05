{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module PlutusTx.Test.Golden (
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

  -- * Golden evaluation testing
  goldenEvalCek,
  goldenEvalCekCatch,
  goldenEvalCekCatchBudget,
  goldenEvalCekLog,

  -- * Combined testing
  goldenBundle,
  goldenBundle',
) where

import Prelude

import Control.Lens (Field1 (_1), view)
import Control.Monad.Except (runExceptT)
import Data.Text (Text)
import Flat (Flat)
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget qualified as PLC
import PlutusCore.Pretty (Pretty (pretty), PrettyBy (prettyBy), PrettyConfigClassic,
                          PrettyConfigName, PrettyUni, Render (render), prettyClassicSimple,
                          prettyPlcClassicSimple, prettyReadable, prettyReadableSimple)
import PlutusCore.Test (TestNested, ToUPlc (..), goldenSize, goldenTPlc, goldenUPlc,
                        goldenUPlcReadable, nestedGoldenVsDoc, nestedGoldenVsDocM, ppCatch, rethrow,
                        runUPlcBudget)
import PlutusIR.Core.Type (progTerm)
import PlutusIR.Test ()
import PlutusTx.Code (CompiledCode, CompiledCodeIn, getPir, getPirNoAnn)
import PlutusTx.Test.Orphans ()
import PlutusTx.Test.Run.Uplc (runPlcCek, runPlcCekBudget, runPlcCekTrace)
import Test.Tasty (TestName)
import Test.Tasty.Extras ()
import UntypedPlutusCore qualified as UPLC

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
  goldenEvalCekCatch name y
  goldenBudget name y

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
  => TestName
  -> a
  -> TestNested
goldenEvalCek name values =
  nestedGoldenVsDocM name ".eval" $
    prettyPlcClassicSimple <$> rethrow (runPlcCek values)

goldenEvalCekCatch
  :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun)
  => TestName -> a -> TestNested
goldenEvalCekCatch name values =
  nestedGoldenVsDocM name ".eval" $
    either (pretty . show) prettyPlcClassicSimple
      <$> runExceptT (runPlcCek values)

goldenEvalCekLog
  :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun)
  => TestName -> a -> TestNested
goldenEvalCekLog name values =
  nestedGoldenVsDocM name ".eval" $
    prettyPlcClassicSimple . view _1 <$> rethrow (runPlcCekTrace values)

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
