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
import Evaluation.Machines
import Evaluation.Regressions (schnorrVerifyRegressions)
import Flat.Spec (test_flat)
import Generators (test_parsing)
import Transform.Simplify (test_simplify)

import Test.Tasty

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultMain $ testGroup "Untyped Plutus Core"
    [ test_machines
    , test_builtins
    , test_budget
    , test_golden
    , test_tallying
    , test_simplify
    , test_debruijn
    , test_freevars
    , test_parsing
    , test_debug
    , test_flat
    , schnorrVerifyRegressions
    , evalOrder
    ]
