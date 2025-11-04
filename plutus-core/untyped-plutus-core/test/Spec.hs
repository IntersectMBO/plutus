{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import GHC.IO.Encoding (setLocaleEncoding, utf8)

import Analysis.Spec (evalOrder)
import DeBruijn.Spec (test_debruijn)
import Evaluation.Builtins (test_builtins)
import Evaluation.Debug (test_debug)
import Evaluation.FreeVars (test_freevars)
import Evaluation.Golden (test_golden)
import Evaluation.Machines (test_NumberOfStepCounters, test_budget, test_machines, test_tallying)
import Evaluation.Regressions (schnorrVerifyRegressions)
import Generators.Spec (test_parsing)
import Scoping.Spec (test_names)
import Transform.CaseOfCase.Spec (test_caseOfCase)
import Transform.Inline.Spec (test_inline)
import Transform.Simplify.Spec (test_simplify)

import Test.Tasty

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultMain $
    testGroup
      "Untyped Plutus Core"
      [ test_machines
      , test_builtins
      , test_budget
      , test_caseOfCase
      , test_inline
      , test_golden
      , test_tallying
      , test_NumberOfStepCounters
      , test_simplify
      , test_debruijn
      , test_freevars
      , test_parsing
      , test_debug
      , schnorrVerifyRegressions
      , evalOrder
      , test_names
      ]
