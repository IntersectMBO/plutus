-- editorconfig-checker-disable-file
{-# LANGUAGE GADTs #-}

module Cardano.Constitution.Validator.Data.GoldenTests
    ( tests
    ) where

import Cardano.Constitution.Config
import Cardano.Constitution.Data.Validator
import Cardano.Constitution.Validator.TestsCommon
import Helpers.TestBuilders
import PlutusCore.Default as UPLC
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Pretty (prettyPlcReadableSimple)
import PlutusLedgerApi.V3 as V3
import PlutusLedgerApi.V3.ArbitraryContexts as V3
import PlutusTx.Code as Tx
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek as UPLC

import Data.ByteString.Short qualified as SBS
import Data.Map.Strict qualified as M
import Data.Maybe
import Data.String
import System.FilePath
import Test.Tasty
import Test.Tasty.Golden

import Helpers.Guardrail

-- The golden files may change, so use `--accept` in cabal `--test-options` to accept the changes **after reviewing them**.

test_cbor, test_budget_small, test_budget_large, test_readable_pir, test_readable_uplc :: TestTree

test_cbor = testGroup "Cbor" $ M.elems $
    (\vName (_, vCode) ->
         -- The unit of measurement is in bytes
         goldenVsString vName (mkPath vName ["cbor","size"]) $
            pure $ fromString $ show $ SBS.length $ V3.serialiseCompiledCode vCode
    ) `M.mapWithKey` defaultValidatorsWithCodes

test_budget_large = testGroup "BudgetLarge" $ M.elems $
    (\vName (_, vCode) ->
         -- The unit of measurement is in execution steps.
         -- See maxTxExSteps, maxTxExMem for limits for chain limits: <https://beta.explorer.cardano.org/en/protocol-parameters/>
         goldenVsString vName (mkPath vName ["large","budget"]) $
            pure $ fromString $ show $ runForBudget vCode $ V3.mkFakeParameterChangeContext getFakeLargeParamsChange -- mkLargeFakeProposal defaultConstitutionConfig
    )`M.mapWithKey` defaultValidatorsWithCodes

test_budget_small = testGroup "BudgetSmall" $ M.elems $
    (\vName (_, vCode) ->
         -- The unit of measurement is in execution steps.
         -- See maxTxExSteps, maxTxExMem for limits for chain limits: <https://beta.explorer.cardano.org/en/protocol-parameters/>
         goldenVsString vName (mkPath vName ["small","budget"]) $
            pure $ fromString $ show $ runForBudget vCode $ V3.mkSmallFakeProposal defaultConstitutionConfig
    )`M.mapWithKey` defaultValidatorsWithCodes

test_readable_pir = testGroup "ReadablePir" $ M.elems $
    (\vName (_, vCode) ->
         goldenVsString vName (mkPath vName ["pir"]) $
            pure $ fromString $ show $ prettyPlcReadableSimple $ fromJust $ getPirNoAnn vCode
    )`M.mapWithKey` defaultValidatorsWithCodes

test_readable_uplc = testGroup "ReadableUplc" $ M.elems $
    (\vName (_, vCode) ->
         goldenVsString vName (mkPath vName ["uplc"]) $
            pure $ fromString $ show $ prettyPlcReadableSimple $ getPlcNoAnn vCode
    )`M.mapWithKey` defaultValidatorsWithCodes

tests :: TestTreeWithTestState
tests = testGroup' "Golden" $ fmap const
        [ test_cbor
        , test_budget_large
        , test_budget_small
        , test_readable_pir
        , test_readable_uplc
        ]

-- HELPERS

mkPath :: String -> [String] -> FilePath
mkPath vName exts = foldl1 (</>) ["test","Cardano","Constitution","Validator","Data","GoldenTests", foldl (<.>) vName ("golden" : exts)]

runForBudget :: (ToData ctx)
             => CompiledCode ConstitutionValidator
             -> ctx
             -> ExBudget
runForBudget v ctx =
        let vPs = UPLC._progTerm $ getPlcNoAnn $ v
                  `unsafeApplyCode` liftCode110 (unsafeFromBuiltinData . toBuiltinData $ ctx)
        in case UPLC.runCekDeBruijn defaultCekParametersForTesting counting noEmitter vPs of
                -- Here, we guard against the case that a ConstitutionValidator **FAILS EARLY** (for some reason),
                -- resulting in misleading low budget costs.
                UPLC.CekReport (UPLC.CekSuccessConstant (UPLC.Some (UPLC.ValueOf UPLC.DefaultUniUnit ()))) (UPLC.CountingSt budget) _ -> budget
                _ -> error "For safety, we only compare budgets of successful executions."
