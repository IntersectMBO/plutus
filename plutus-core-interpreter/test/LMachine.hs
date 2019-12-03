-- | The L machine tests.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module LMachine
    ( test_evaluateL
    ) where

import           PlcTestUtils

import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.Generators.Test
import           Language.PlutusCore.Interpreter.LMachine

import           Test.Tasty
import           Test.Tasty.Hedgehog

test_evaluateL :: TestTree
test_evaluateL =
    testGroup "evaluateL"
        [ testGroup "props" $ fromInterestingTermGens $ \name ->
            testProperty name . propEvaluate @LMachineError (pureTry . evaluateL)
        ]
