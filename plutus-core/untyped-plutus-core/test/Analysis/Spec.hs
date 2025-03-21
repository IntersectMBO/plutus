{-# LANGUAGE OverloadedStrings #-}

module Analysis.Spec where

import Analysis.Spec.Lib

import Test.Tasty (TestTree)
import Test.Tasty.Extras (embed, runTestNested)
import Test.Tasty.HUnit (testCase, (@=?))
import UntypedPlutusCore.Purity (termEvaluationOrder, unEvalOrder)

evalOrder :: TestTree
evalOrder =
  runTestNested
    ["untyped-plutus-core", "test", "Analysis", "evalOrder"]
    [ goldenEvalOrder "letFun" letFun
    , goldenEvalOrder "letImpure" letImpure
    , embed testEvalOrderIsLazy
    ]

testEvalOrderIsLazy :: TestTree
testEvalOrderIsLazy =
  testCase "evalOrderLazy" $
    let order = termEvaluationOrder builtinSemantics dangerTerm
        subterms = unEvalOrder order
     in 4 @=? length subterms
