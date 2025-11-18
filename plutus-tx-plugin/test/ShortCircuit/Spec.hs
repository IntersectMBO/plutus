{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module ShortCircuit.Spec (tests) where

import ShortCircuit.WithGHCOptimisations qualified as WithOptimisations
import ShortCircuit.WithoutGHCOptimisations qualified as WithoutOptimisations

import Control.Lens ((&))
import PlutusCore.Default (DefaultFun, DefaultUni, someValue)
import PlutusTx.Code (CompiledCode, unsafeApplyCode)
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.TH (compile)
import PlutusTx.Test.Run.Code (evalResult, evaluateCompiledCode)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertEqual, assertFailure, testCase)
import UntypedPlutusCore.Core.Type (Term (Constant))
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal (NTerm)

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
assertResult expected code =
  case evalResult (evaluateCompiledCode code) of
    Left ex -> assertFailure $ show ex
    Right actual -> assertEqual "Evaluation has succeeded" expected actual

false' :: CompiledCode Bool
false' = liftCodeDef False

true' :: CompiledCode Bool
true' = liftCodeDef True

termFalse :: NTerm DefaultUni DefaultFun ()
termFalse = Constant () $ someValue False

termTrue :: NTerm DefaultUni DefaultFun ()
termTrue = Constant () $ someValue True
