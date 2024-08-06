{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

module ShortCircuit.Spec (tests) where

import ShortCircuit.WithGHCOptimisations qualified as WithOptimisations
import ShortCircuit.WithoutGHCOptimisations qualified as WithoutOptimisations

import Control.Lens ((&), (^.))
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import PlutusTx.Code (CompiledCode, getPlc, unsafeApplyCode)
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.TH (compile)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertEqual, assertFailure, testCase)
import UntypedPlutusCore.Core.Type (Term (Constr), progTerm)
import UntypedPlutusCore.Evaluation.Machine.Cek (counting, noEmitter)
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal (NTerm, runCekDeBruijn)

-- These tests are here to ensure that the short-circuiting behaviour of the logical operators
-- is preserved when the code is compiled with and without GHC optimisations.
-- See also Note [Lazy boolean operators] in the plugin.
tests :: TestTree
tests =
  testGroup
    "ShortCircuiting operators"
    [ testCase "(&&) short-circuits with GHC optimisations" $
        unsafeApplyCode $$(compile [||WithOptimisations.shortCircuitAnd||]) false'
          & assertResult termFalse
    , testCase "(||) short-circuits with GHC optimisations" do
        unsafeApplyCode $$(compile [||WithOptimisations.shortCircuitOr||]) true'
          & assertResult termTrue
    , testCase "(&&) short-circuits without GHC optimisations" $
        unsafeApplyCode $$(compile [||WithoutOptimisations.shortCircuitAnd||]) false'
          & assertResult termFalse
    , testCase "(||) short-circuits without GHC optimisations" do
        unsafeApplyCode $$(compile [||WithoutOptimisations.shortCircuitOr||]) true'
          & assertResult termTrue
    ]

----------------------------------------------------------------------------------------------------
-- Helpers -----------------------------------------------------------------------------------------

assertResult :: NTerm DefaultUni DefaultFun () -> CompiledCode a -> Assertion
assertResult expected code = do
  let plc = getPlc code ^. progTerm
  case runCekDeBruijn defaultCekParametersForTesting counting noEmitter plc of
    (Left ex, _counting, _logs)      -> assertFailure $ show ex
    (Right actual, _counting, _logs) -> assertEqual "Evaluation has succeeded" expected actual

false' :: CompiledCode Bool
false' = liftCodeDef False

true' :: CompiledCode Bool
true' = liftCodeDef True

termFalse :: Term name uni fun ()
termFalse = Constr mempty 1 []

termTrue :: Term name uni fun ()
termTrue = Constr mempty 0 []
