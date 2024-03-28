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
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParameters)
import PlutusTx.Code (CompiledCode, getPlc, unsafeApplyCode)
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.TH (compile)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertEqual, assertFailure, testCase)
import UntypedPlutusCore.Core.Type (Term (Constr), progTerm)
import UntypedPlutusCore.Evaluation.Machine.Cek (counting, noEmitter)
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal (NTerm, runCekDeBruijn)

tests :: TestTree
tests = testGroup "ShortCircuit" [withGhcOptimisations, withoutGhcOptimisations]

withGhcOptimisations :: TestTree
withGhcOptimisations =
  testGroup
    "GHC Optimisations ON"
    [ testCase "GHC inlines the (&&) unfolding making it short-circuit" $
        unsafeApplyCode $$(compile [||WithOptimisations.shortCircuitAnd||]) false'
          & assertResult termFalse
    , testCase "GHC inlines the (||) unfolding making it short-circuit" do
        unsafeApplyCode $$(compile [||WithOptimisations.shortCircuitOr||]) true'
          & assertResult termTrue
    ]

withoutGhcOptimisations :: TestTree
withoutGhcOptimisations =
  testGroup
    "GHC Optimisations OFF"
    [ testCase "(&&) isn't inlined but it short-circuits anyway" do
        unsafeApplyCode $$(compile [||WithoutOptimisations.shortCircuitAnd||]) false'
          & assertResult termFalse
    , testCase "(||) isn't inlined but it short-circuits anyway" do
        unsafeApplyCode $$(compile [||WithoutOptimisations.shortCircuitOr||]) true'
          & assertResult termTrue
    ]

----------------------------------------------------------------------------------------------------
-- Helpers -----------------------------------------------------------------------------------------

assertResult :: NTerm DefaultUni DefaultFun () -> CompiledCode a -> Assertion
assertResult expected code =
  case runCekDeBruijn defaultCekParameters counting noEmitter (getPlc code ^. progTerm) of
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
