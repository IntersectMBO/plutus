module BuiltinCasing.TargetVersion.Spec (tests) where

import BuiltinCasing.TargetVersion.V110 qualified as V110
import BuiltinCasing.TargetVersion.V120 qualified as V120
import PlutusCore.Builtin (CaserBuiltin (..))
import PlutusCore.Data (Data (Constr, I))
import PlutusCore.Default (caseBuiltinNoData, someValue)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import PlutusCore.Evaluation.Machine.MachineParameters (MachineParameters (..))
import PlutusCore.Version (Version, plcVersion110, plcVersion120)
import PlutusTx.Builtins (BuiltinData)
import PlutusTx.Builtins.Internal (dataToBuiltinData)
import PlutusTx.Code (CompiledCode, getPlcNoAnn, unsafeApplyCode)
import PlutusTx.Eval (EvalResult (..), evaluateCompiledCode')
import PlutusTx.Lift (liftCode)
import Test.Tasty (TestName, TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import UntypedPlutusCore qualified as UPLC

-- Regression for plutus-private#2465: decoding must work with either target version.
tests :: TestTree
tests =
  testGroup
    "BuiltinCasing.TargetVersion"
    [ decodingTests "1.1.0" plcVersion110 V110.decodeAB V110.decodeMaybe
    , decodingTests "1.2.0" plcVersion120 V120.decodeAB V120.decodeMaybe
    ]

decodingTests
  :: TestName
  -> Version
  -> CompiledCode (BuiltinData -> Integer)
  -> CompiledCode (BuiltinData -> Integer)
  -> TestTree
decodingTests name version decodeAB decodeMaybe =
  testGroup
    name
    [ assertDecodes version "A" decodeAB (Constr 0 []) 0
    , assertDecodes version "B" decodeAB (Constr 1 []) 1
    , assertDecodes version "Just" decodeMaybe (Constr 0 [I 7]) 7
    , assertDecodes version "Nothing" decodeMaybe (Constr 1 []) 0
    ]

assertDecodes
  :: Version
  -> TestName
  -> CompiledCode (BuiltinData -> Integer)
  -> Data
  -> Integer
  -> TestTree
assertDecodes version name decoder input expected = testCase name $ do
  UPLC._progVer (getPlcNoAnn decoder) @?= version
  let applied = decoder `unsafeApplyCode` liftCode version (dataToBuiltinData input)
      -- The default test evaluator allows Data casing; 1.1.0 does not.
      params =
        if version == plcVersion110
          then
            defaultCekParametersForTesting
              { machineCaserBuiltin = CaserBuiltin caseBuiltinNoData
              }
          else defaultCekParametersForTesting
  case evalResult (evaluateCompiledCode' params applied) of
    Left err -> assertFailure (show err)
    Right result -> result @?= UPLC.Constant () (someValue expected)
