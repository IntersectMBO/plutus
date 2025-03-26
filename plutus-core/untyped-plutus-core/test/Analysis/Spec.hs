{-# LANGUAGE OverloadedStrings #-}

module Analysis.Spec where

import Analysis.Spec.Lib

import PlutusCore.Default (DefaultFun (..), DefaultUni)
import PlutusCore.MkPlc (mkConstant)
import PlutusCore.Name.Unique (Name)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Extras (embed, runTestNested)
import Test.Tasty.HUnit (testCase, (@=?), (@?=))
import UntypedPlutusCore (Term)
import UntypedPlutusCore.Core.Type (Term (Apply, Builtin, Force))
import UntypedPlutusCore.Purity (isPure, termEvaluationOrder, unEvalOrder)

evalOrder :: TestTree
evalOrder =
  runTestNested
    ["untyped-plutus-core", "test", "Analysis", "evalOrder"]
    [ goldenEvalOrder "letFun" letFun
    , goldenEvalOrder "letImpure" letImpure
    , embed testEvalOrderIsLazy
    , embed $
        testGroup
          "Purity"
          [ testSomeTypeSomeTermArgsLeft
          , testNoTypeSomeTermArgsLeft
          , testNoTypeNoTermArgsLeft
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
      - CaseList   : [ forall a, forall b
                      , b
                      , (fun a (fun [ (con list) a ] b))
                      , list(a)
                      ] -> b

  When it comes to purity of builtin terms,
  we want to test the following cases:
  +---------------+---------------+--------+
  | Type args     | Term args     | Purity |
  | left to apply | left to apply |        |
  +---------------+---------------+--------+
  |     some      |     some      | Impure |
  |     none      |     some      | Pure   |
  |     none      |     none      | Impure |
  +---------------+---------------+--------+
-}

testSomeTypeSomeTermArgsLeft :: TestTree
testSomeTypeSomeTermArgsLeft =
  testCase "some type args and some term args are unapplied -> Impure" $
    map (isPure builtinSemantics) terms @?= [False, False]
 where
  terms :: [Term Name DefaultUni DefaultFun ()] =
    [ Builtin () Trace -- 1 type arg and 2 term args are unapplied
    , Force () (Builtin () FstPair) -- 2 type args, 1 applied and 1 left
    ]

testNoTypeSomeTermArgsLeft :: TestTree
testNoTypeSomeTermArgsLeft =
  testCase "no type args and some term args are unapplied -> Pure" $
    map (isPure builtinSemantics) terms @?= [True, True]
 where
  terms :: [Term Name DefaultUni DefaultFun ()] =
    [ Builtin () EncodeUtf8 -- no type args, 1 term arg left to apply
    , Force () (Builtin () Trace) -- 1 type arg applied, 2 term args left
    ]

testNoTypeNoTermArgsLeft :: TestTree
testNoTypeNoTermArgsLeft =
  testCase "no type args and no term args are unapplied -> Impure" $
    map (isPure builtinSemantics) terms @?= [False, False]
 where
  terms :: [Term Name DefaultUni DefaultFun ()] =
    [ Apply () (Apply () (Builtin () AddInteger) two) two
    , Apply
        ()
        ( Apply
            ()
            (Apply () (Force () (Builtin () IfThenElse)) yes)
            two
        )
        two
    ]

  two :: Term Name DefaultUni DefaultFun ()
  two = mkConstant () (2 :: Integer)

  yes :: Term Name DefaultUni DefaultFun ()
  yes = mkConstant () True
