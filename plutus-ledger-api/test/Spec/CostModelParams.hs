{-# LANGUAGE TypeApplications #-}
module Spec.CostModelParams where

import Plutus.V1.Ledger.EvaluationContext as V1
import Plutus.V2.Ledger.EvaluationContext as V2

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
import Data.Text qualified as Text
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "costModelParams"
    [ testCase "length" $ do
            166 @=? length (enumerate @V1.ParamName)
            166 @=? length V1.costModelParamNames
            175 @=? length (enumerate @V2.ParamName)
            175 @=? length V2.costModelParamNames
    , testCase "text" $ do
            -- this depends on the fact that V1/V2 are alphabetically-ordered; does not have to hold for future versions
            altV1CostModelParamNames @=? V1.costModelParamNames
            -- this depends on the fact that V1/V2 are alphabetically-ordered; does not have to hold for future versions
            Map.keys (fromJust Plutus.defaultCostModelParams) @=? V2.costModelParamNames
    , testCase "context length" $ do
            let defaultCostValues = Map.elems $ fromJust defaultCostModelParams
            -- the defaultcostmodelparams reflects only the latest version V2, so this should succeed because the lengths match
            assertBool "wrong number of arguments in V2.mkContext" $ isRight $ V2.mkEvaluationContext defaultCostValues
            -- this one should not succeed because V1 evaluation-context expects less number of arguments.
            assertBool "wrong number of arguments in V1.mkContext" $ isLeft $ V1.mkEvaluationContext defaultCostValues
    ]


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
