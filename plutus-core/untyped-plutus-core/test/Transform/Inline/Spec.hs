{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE NumericUnderscores  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Transform.Inline.Spec where

import Control.Monad.Reader (runReaderT)
import Control.Monad.State (runStateT)
import Data.MultiSet qualified as MultiSet
import PlutusCore.Annotation (Inline (MayInline))
import PlutusCore.Quote (runQuote)
import PlutusCore.Size (Size (..))
import PlutusPrelude (def)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase)
import UntypedPlutusCore (DefaultFun, DefaultUni, Name (..), Term (..))
import UntypedPlutusCore.Test.Term.Construction (addInteger, uniqueNames3, var)
import UntypedPlutusCore.Transform.Inline (InlineHints (InlineHints), InlineInfo (..), InlineM,
                                           S (..), Subst (Subst), TermEnv (TermEnv),
                                           isFirstVarBeforeEffects)

--------------------------------------------------------------------------------
-- Tests -----------------------------------------------------------------------

test_inline :: TestTree
test_inline =
  testGroup
    "isFirstVarBeforeEffects"
    [ testCase "before effects" testVarBeforeEffects
    , testCase "after effects" testVarAfterEffects
    ]

testVarBeforeEffects :: IO ()
testVarBeforeEffects = do
  assertBool "a is evaluated before effects" do
    testFirstVarBeforeEffects a term
  assertBool "b is evaluated before effects" do
    testFirstVarBeforeEffects b term

testVarAfterEffects :: IO ()
testVarAfterEffects = do
  assertBool "c is not evaluated after effects" $ not do
    testFirstVarBeforeEffects c term

--------------------------------------------------------------------------------
-- Test terms ------------------------------------------------------------------

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

a, b, c :: Name
(a, b, c) = uniqueNames3 "a" "b" "c"

--------------------------------------------------------------------------------
-- Helper functions: -----------------------------------------------------------

testFirstVarBeforeEffects :: Name -> Term Name DefaultUni DefaultFun () -> Bool
testFirstVarBeforeEffects name = runInlineM . isFirstVarBeforeEffects name

runInlineM :: InlineM Name DefaultUni DefaultFun () r -> r
runInlineM m = result
 where
  (result, _finalState) =
    runQuote (runStateT (runReaderT m inlineInfo) initialState)

  inlineInfo :: InlineInfo Name DefaultFun ()
  inlineInfo =
    InlineInfo
      { _iiUsages = MultiSet.empty
      , _iiHints = InlineHints \_ann _name -> MayInline
      , _iiBuiltinSemanticsVariant = def
      , _iiInlineConstants = True
      , _iiInlineCallsiteGrowth = Size 1_000_000
      }

  initialState :: S Name DefaultUni DefaultFun ()
  initialState = S{_subst = Subst (TermEnv mempty), _vars = mempty}
