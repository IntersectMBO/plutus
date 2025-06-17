{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module PlutusTx.Test.Golden (
  -- * TH CodGen
  goldenCodeGen,

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
  goldenEvalCekTraceCatchBudget,
  goldenEvalCekLog,

  -- * Combined testing
  goldenBundle,
  goldenBundle',

  -- * Pretty-printing
  prettyBudget,
) where

import Prelude

import Control.Lens (Field1 (_1), view, (^.))
import Control.Monad.Except (runExceptT)
import Data.List qualified as List
import Data.SatInt (fromSatInt)
import Data.Text (Text)
import Flat (Flat)
import Language.Haskell.TH qualified as TH
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusCore.Pretty (Doc, Pretty (pretty), PrettyBy (prettyBy), PrettyConfigClassic,
                          PrettyConfigName, PrettyUni, Render (render), prettyClassicSimple,
                          prettyPlcClassicSimple, prettyReadable, prettyReadableSimple)
import PlutusCore.Size (Size (..))
import PlutusCore.Test (TestNested, ToUPlc (..), goldenSize, goldenTPlc, goldenUPlc,
                        goldenUPlcReadable, nestedGoldenVsDoc, nestedGoldenVsDocM, ppCatch, rethrow,
                        runUPlcBudget)
import PlutusIR.Core.Type (progTerm)
import PlutusIR.Test ()
import PlutusTx.Code (CompiledCode, CompiledCodeIn, getPir, getPirNoAnn)
import PlutusTx.Test.Orphans ()
import PlutusTx.Test.Run.Uplc (runPlcCek, runPlcCekBudget, runPlcCekTrace)
import Prettyprinter (fill, vsep, (<+>))
import Test.Tasty (TestName)
import Test.Tasty.Extras ()
import Text.Printf (printf)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC


-- Value assertion tests
goldenCodeGen :: TH.Ppr a => TestName -> TH.Q a -> TH.ExpQ
goldenCodeGen name code = do
  c <- code
  [| nestedGoldenVsDoc name ".th" $(TH.stringE $ TH.pprint c) |]

goldenBudget :: TestName -> CompiledCode a -> TestNested
goldenBudget name compiledCode = do
  nestedGoldenVsDocM name ".budget" $ ppCatch $ do
    budget <- runUPlcBudget [compiledCode]
    size <- UPLC.programSize <$> toUPlc compiledCode
    pure (render @Text (prettyBudget budget size))

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
  => TestName
  -> a
  -> TestNested
goldenEvalCek name value =
  nestedGoldenVsDocM name ".eval" $
    prettyPlcClassicSimple <$> rethrow (runPlcCek value)

goldenEvalCekCatch
  :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun)
  => TestName -> a -> TestNested
goldenEvalCekCatch name value =
  nestedGoldenVsDocM name ".eval" $
    either (pretty . show) prettyPlcClassicSimple
      <$> runExceptT (runPlcCek value)

goldenEvalCekCatchBudget :: TestName -> CompiledCode a -> TestNested
goldenEvalCekCatchBudget name compiledCode =
  nestedGoldenVsDocM name ".eval" $ ppCatch $ do
    (termRes, budget) <- runPlcCekBudget compiledCode
    size <- UPLC.programSize <$> toUPlc compiledCode
    let contents =
          vsep
            [ prettyBudget budget size
            , mempty
            , prettyPlcClassicSimple termRes
            ]
    pure (render @Text contents)

goldenEvalCekTraceCatchBudget :: TestName -> CompiledCode a -> TestNested
goldenEvalCekTraceCatchBudget name compiledCode =
  nestedGoldenVsDocM name ".eval" . ppCatch $ do
    term <- toUPlc compiledCode
    let
      (evalRes, UPLC.CountingSt budget, logOut) =
        UPLC.runCek
          PLC.defaultCekParametersForTesting
          UPLC.counting
          UPLC.logEmitter
          (term ^. UPLC.progTerm)
      size = UPLC.programSize term

      traceMsg =
        case logOut of
          [] -> ["Trace: <empty>"]
          x ->
              [ "Trace:"
              , vsep $ pretty <$> x
              ]

    case evalRes of
      Left evalErr ->
        pure $
          render @Text $
            vsep
              [ prettyReadable evalErr
              , mempty
              , vsep traceMsg
              ]
      Right termRes ->
        pure $
          render @Text $
            vsep
              [ prettyBudget budget size
              , mempty
              , vsep traceMsg
              , mempty
              , prettyPlcClassicSimple termRes
              ]

goldenEvalCekLog
  :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun)
  => TestName -> a -> TestNested
goldenEvalCekLog name value =
  nestedGoldenVsDocM name ".eval" $
    prettyPlcClassicSimple . view _1 <$> rethrow (runPlcCekTrace value)

prettyBudget :: PLC.ExBudget -> Size -> Doc ann
prettyBudget (PLC.ExBudget (ExCPU cpu) (ExMemory mem)) (Size size) =
  vsep
    [ fill 8 "CPU:" <+> prettyIntRightAligned (fromSatInt @Int cpu)
    , fill 8 "Memory:" <+> prettyIntRightAligned (fromSatInt @Int mem)
    , fill 8 "Size:" <+> prettyIntRightAligned size
    ]
 where
  prettyIntRightAligned :: (Integral i) => i -> Doc ann
  prettyIntRightAligned =
    pretty @String
      . printf "%19s"
      . reverse
      . List.intercalate "_"
      . chunksOf 3
      . reverse
      . show @Integer
      . fromIntegral
   where
    chunksOf _ [] = []
    chunksOf n xs = take n xs : chunksOf n (drop n xs)
