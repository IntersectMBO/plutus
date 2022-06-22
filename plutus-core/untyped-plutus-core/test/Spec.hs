{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module Main where

import GHC.IO.Encoding (setLocaleEncoding, utf8)

import DeBruijn.Spec (test_debruijn)
import Evaluation.Builtins (test_builtins)
import Evaluation.FreeVars (test_freevars)
import Evaluation.Golden (test_golden)
import Evaluation.Machines
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
    ]

