{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Transform.Inline.Spec where

import Data.Maybe (fromMaybe, isNothing)
import PlutusPrelude (def)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, testCase)
import UntypedPlutusCore (DefaultFun, DefaultUni, Name (..), Term (..))
import UntypedPlutusCore.Test.Term.Construction (addInteger, app, case_, delay, lam, uniqueNames3,
                                                 uniqueNames4, var)
import UntypedPlutusCore.Transform.Inline (isFirstVarBeforeEffects, isVarDelayed)

test_inline :: TestTree
test_inline =
  testGroup
    "Inline"
    [ testCase
        "var is before or after effects"
        testVarBeforeAfterEffects
    , testGroup
        "isVarDelayed"
        [ testCase
            "a var is delayed if it's inside a delay"
            testVarIsDelayedInDelay
        , testCase
            "a var is delayed if it's inside a lambda"
            testVarDelayedInLambda
        , testCase
            "a var is delayed if it's inside a case branch"
            testVarIsDelayedInCaseBranch
        ]
    ]

testVarBeforeAfterEffects :: Assertion
testVarBeforeAfterEffects = do
  assertBool "a is evaluated before effects" do
    isFirstVarBeforeEffects def a term
  assertBool "b is evaluated before effects" do
    isFirstVarBeforeEffects def b term
  assertBool "c is not evaluated after effects" $ not do
    isFirstVarBeforeEffects def c term
 where
  term :: Term Name DefaultUni DefaultFun ()
  term =
    {- Evaluation order:

      1. pure work-free: a
      2. pure work-free: b
      3. impure? maybe work?: addInteger a b
      4. pure work-free: c
      5. impure? maybe work?: addInteger (addInteger a b) c
    -}
    addInteger (addInteger (var a) (var b)) (var c)
  (a, b, c) = uniqueNames3 "a" "b" "c"

testVarIsDelayedInDelay :: Assertion
testVarIsDelayedInDelay = do
  assertBool "var 'a' is delayed in delay" $
    fromMaybe False (isVarDelayed a term)
  assertBool "var 'b' is not delayed outside of the delay" $
    maybe False not (isVarDelayed b term)
  assertBool "it's not known if var 'c' is delayed" $
    isNothing (isVarDelayed c term)
 where
  term :: Term Name DefaultUni DefaultFun ()
  term = delay (var a `addInteger` var b) `addInteger` var b

  (a, b, c) = uniqueNames3 "a" "b" "c"

testVarDelayedInLambda :: Assertion
testVarDelayedInLambda = do
  assertBool "var 'a' is delayed in lambda body" $
    fromMaybe False (isVarDelayed a term)
  assertBool "var 'c' is not delayed outside of the lambda" $
    maybe False not (isVarDelayed c term)
  assertBool "it's not known if var 'd' is delayed" $
    isNothing (isVarDelayed d term)
 where
  term :: Term Name DefaultUni DefaultFun ()
  term = lam b (var a `addInteger` var c) `app` var c

  (a, b, c, d) = uniqueNames4 "a" "b" "c" "d"

testVarIsDelayedInCaseBranch :: Assertion
testVarIsDelayedInCaseBranch = do
  assertBool "var 'a' is delayed in case branch" $
    fromMaybe False (isVarDelayed a term)
  assertBool "var 'b' is not delayed outside of the case branch" $
    maybe False not (isVarDelayed b term)
  assertBool "it is not know if var 'd' is delayed or not" $
    isNothing (isVarDelayed d term)
 where
  term :: Term Name DefaultUni DefaultFun ()
  term = case_ (var b) [var a, var b, var c]

  (a, b, c, d) = uniqueNames4 "a" "b" "c" "d"
