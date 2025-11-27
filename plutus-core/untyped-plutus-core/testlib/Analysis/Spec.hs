{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Analysis.Spec where

import Analysis.Lib
import PlutusCore.Default (DefaultFun (..), DefaultUni)
import PlutusCore.Name.Unique (Name (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Extras (embed, runTestNested)
import Test.Tasty.HUnit (testCase, (@=?), (@?=))
import UntypedPlutusCore (Term (Apply, Builtin, Force))
import UntypedPlutusCore.Purity (isPure, termEvaluationOrder, unEvalOrder)

evalOrder :: TestTree
evalOrder =
  runTestNested
    ["untyped-plutus-core", "test", "Analysis", "evalOrder"]
    [ goldenEvalOrder "letFun" letFun
    , goldenEvalOrder "letImpure" letImpure
    , goldenEvalOrder "ifThenElse" termIfThenElse
    , embed testEvalOrderIsLazy
    , embed $
        testGroup
          "Purity"
          [ testSomeTypeSomeTermArgsLeft
          , testNoTypeSomeTermArgsLeft
          , testNoTypeNoTermArgsLeft
          , testForceNoTypeParam
          , testApplyNoTermParam
          ]
    ]

testEvalOrderIsLazy :: TestTree
testEvalOrderIsLazy =
  testCase "evalOrderLazy" $
    let order = termEvaluationOrder builtinSemantics dangerTerm
        subterms = unEvalOrder order
     in 4 @=? length subterms

{-

  Builtin functions can in theory have their type- and term- arguments
  interleaved arbitrarily, but in the default set of builtins ('DefaultFun')
  we have the following patterns:

  - Builtin functions with 0 type arguments followed by N>0 term arguments:
      - EncodeUtf8 : [ string ] -> bytestring
      - AddInteger : [ integer, integer ] -> integer
      - WriteBits  : [ bytestring, list(integer), bool ] -> bytestring

  - Builtin functions with 1 type argument followed by N>0 term arguments:
      - HeadList   : [ forall a, list(a) ] -> a
      - Trace      : [ forall a, string, a ] -> a
      - IfThenElse : [ forall a, bool, a, a ] -> a

  - Builtin functions with 2 type arguments followed by N>0 term arguments:
      - FstPair    : [ forall a, forall b, pair(a, b) ] -> a
      - ChooseList : [ forall a, forall b, list(a), b, b ] -> b

  When it comes to purity of builtin terms,
  we want to test the following cases:
  +---------------+---------------+
  | Type args     | Term args     |
  | left to apply | left to apply |
  +---------------+---------------+
  |     some      |     some      |
  |     none      |     some      |
  |     none      |     none      |
  +---------------+---------------+
-}

testSomeTypeSomeTermArgsLeft :: TestTree
testSomeTypeSomeTermArgsLeft =
  testCase "some type args and some term args are unapplied" $
    map (isPure builtinSemantics) terms @?= [True, True]
  where
    terms :: [Term Name DefaultUni DefaultFun ()] =
      [ Builtin () Trace -- 1 type arg and 2 term args are unapplied
      , Force () (Builtin () FstPair) -- 2 type args, 1 applied and 1 left
      ]

testNoTypeSomeTermArgsLeft :: TestTree
testNoTypeSomeTermArgsLeft =
  testCase "no type args and some term args are unapplied" $
    map (isPure builtinSemantics) terms @?= [True, True]
  where
    terms :: [Term Name DefaultUni DefaultFun ()] =
      [ Builtin () EncodeUtf8 -- no type args, 1 term arg left to apply
      , Force () (Builtin () Trace) -- 1 type arg applied, 2 term args left
      ]

testNoTypeNoTermArgsLeft :: TestTree
testNoTypeNoTermArgsLeft =
  testGroup
    "no type args and no term args are unapplied"
    [ testAddInteger
    , testIfThenElse
    ]
  where
    testAddInteger :: TestTree =
      testCase "AddInteger" $ isPure builtinSemantics term @?= False
      where
        term :: Term Name DefaultUni DefaultFun () =
          Apply () (Apply () (Builtin () AddInteger) (termVar 1)) (termVar 2)

    testIfThenElse :: TestTree =
      testCase "IfThenElseApplied" $
        isPure builtinSemantics termIfThenElse @?= False

testForceNoTypeParam :: TestTree
testForceNoTypeParam =
  testCase "forcing a non-existing type param is impure" $
    isPure builtinSemantics (Force () (Builtin () EncodeUtf8)) @?= False

testApplyNoTermParam :: TestTree
testApplyNoTermParam =
  testGroup
    "invalid application of a term param is impure"
    [ testCase "when a type param is expected" $
        isPure builtinSemantics termExpectingType @?= False
    , testCase "when a builtin is saturated" $
        isPure builtinSemantics termSaturated @?= False
    ]
  where
    termExpectingType :: Term Name DefaultUni DefaultFun () =
      Apply () (Builtin () Trace) (termVar 1)
    termSaturated :: Term Name DefaultUni DefaultFun () =
      Apply () (Builtin () EncodeUtf8) (termVar 1)
