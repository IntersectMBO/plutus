-- editorconfig-checker-disable-file
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Evaluation.Machines
  ( test_machines
  )
where

import GHC.Exts (fromString)
import PlutusCore
import PlutusCore.Evaluation.Machine.Ck
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Generators.Hedgehog.Interesting
import PlutusCore.Generators.Hedgehog.Test
import PlutusCore.Pretty
import PlutusCore.Test

import Data.Default.Class (def)
import Test.Tasty
import Test.Tasty.Hedgehog

testMachine
  :: (uni ~ DefaultUni, fun ~ DefaultFun, PrettyPlc structural)
  => String
  -> ( Term TyName Name uni fun ()
       -> Either
            (EvaluationException structural operational (Term TyName Name uni fun ()))
            (Term TyName Name uni fun ())
     )
  -> TestTree
testMachine machine eval =
  testGroup machine $ fromInterestingTermGens $ \name ->
    testPropertyNamed name (fromString name)
      . mapTestLimitAtLeast 50 (`div` 10)
      . propEvaluate eval

test_machines :: TestTree
test_machines =
  testGroup
    "machines"
    [ testMachine "CK" $ evaluateCkNoEmit defaultBuiltinsRuntimeForTesting def
    ]
