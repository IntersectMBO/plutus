-- editorconfig-checker-disable-file
{-# LANGUAGE TypeApplications #-}
module Spec.CostModelParams where

import PlutusLedgerApi.Common
import PlutusLedgerApi.V1 as V1
import PlutusLedgerApi.V2 as V2
import PlutusLedgerApi.V3 as V3

import PlutusCore.Evaluation.Machine.BuiltinCostModel as Plutus
import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults as Plutus
import PlutusCore.Evaluation.Machine.MachineParameters as Plutus

import Barbies
import Control.Lens
import Data.Either
import Data.List.Extra
import Data.Map as Map
import Data.Maybe
import Data.Set as Set
import Data.Text qualified as Text
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "costModelParams"
    [ testCase "length" $ do
            166 @=? length (enumerate @V1.ParamName)
            166 @=? length v1CostModelParamNames
            175 @=? length (enumerate @V2.ParamName)
            175 @=? length v2CostModelParamNames
            175 @=? length (enumerate @V3.ParamName)
            175 @=? length v3CostModelParamNames
    , testCase "text" $ do
            -- this depends on the fact that V1/V2 are alphabetically-ordered; does not have to hold for future versions
            altV1CostModelParamNames @=? v1CostModelParamNames
            -- this depends on the fact that V1/V2 are alphabetically-ordered; does not have to hold for future versions
            Map.keys (fromJust Plutus.defaultCostModelParams) @=? v2CostModelParamNames
    , testCase "context length" $ do
            let defaultCostValues = Map.elems $ fromJust defaultCostModelParams
            -- the defaultcostmodelparams reflects only the latest version V3, so this should succeed because the lengths match
            assertBool "wrong number of arguments in V2.mkContext" $ isRight $ V3.mkEvaluationContext defaultCostValues
            -- currently v2 args ==v3 args
            assertBool "wrong number of arguments in V2.mkContext" $ isRight $ V2.mkEvaluationContext defaultCostValues
            -- this one should not succeed because V1 evaluation-context expects less number of arguments.
            assertBool "wrong number of arguments in V1.mkContext" $ isLeft $ V1.mkEvaluationContext defaultCostValues
    , testCase "cost model parameters" $ do
         -- v1 is missing some cost model parameters because new builtins are added in v2
         assertBool "v1 params is proper subset of v2 params" $ Set.fromList v1CostModelParamNames `Set.isProperSubsetOf` Set.fromList v2CostModelParamNames
         -- v1 is missing some cost model parameters because new builtins are added in v2
         assertBool "v1 params is proper subset of v3 params" $ Set.fromList v1CostModelParamNames `Set.isProperSubsetOf` Set.fromList v3CostModelParamNames
    ]

v1CostModelParamNames :: [Text.Text]
v1CostModelParamNames = Text.pack . showParamName <$> enumerate @V1.ParamName

-- | An alternative, older implementation of calculating V1's costmodelparamnames.
altV1CostModelParamNames :: [Text.Text]
altV1CostModelParamNames = Map.keys $ fromJust $ extractCostModelParams $
   defaultCekCostModel
   & builtinCostModel
   -- here we rely on 'Deriving.Aeson.OmitNothingFields'
   -- to skip jsonifying any fields which are cleared.
   %~ omitV2Builtins
  where
    -- "clears" some fields of builtincostmodel by setting them to Nothing. See 'MCostingFun'.
    omitV2Builtins :: BuiltinCostModel -> BuiltinCostModelBase MCostingFun
    omitV2Builtins bcm =
            -- transform all costing-functions to (Just costingFun)
            (bmap (MCostingFun . Just) bcm)
            {
              -- 'SerialiseData','EcdsaSecp256k1',SchnorrSecp256k1 builtins not available in V1
              paramSerialiseData = mempty
            , paramVerifyEcdsaSecp256k1Signature = mempty
            , paramVerifySchnorrSecp256k1Signature = mempty
            }

v2CostModelParamNames :: [Text.Text]
v2CostModelParamNames = Text.pack . showParamName <$> enumerate @V2.ParamName

v3CostModelParamNames :: [Text.Text]
v3CostModelParamNames = Text.pack . showParamName <$> enumerate @V3.ParamName

