{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE NumericUnderscores  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Transform.Inline.Spec where

import Control.Monad.Reader (runReaderT)
import Control.Monad.State (runStateT)
import Data.MultiSet qualified as MultiSet
import Data.Text qualified as Text
import Numeric.Natural (Natural)
import PlutusCore.Annotation (Inline (MayInline))
import PlutusCore.Default (DefaultFun (AddInteger))
import PlutusCore.Quote (runQuote)
import PlutusCore.Size (Size (..))
import PlutusPrelude (def)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase)
import UntypedPlutusCore (DefaultUni, Name (..), Term (..), Unique (..))
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
  assertBool "var1 is evaluated before effects" do
    testFirstVarBeforeEffects (varName 1) term
  assertBool "var2 is evaluated before effects" do
    testFirstVarBeforeEffects (varName 2) term

testVarAfterEffects :: IO ()
testVarAfterEffects = do
  assertBool "var3 is not evaluated after effects" $ not do
    testFirstVarBeforeEffects (varName 3) term

--------------------------------------------------------------------------------
-- Test term: ------------------------------------------------------------------

term :: Term Name DefaultUni DefaultFun ()
term =
  {- Evaluation order:

    1. pure work-free: var1
    2. pure work-free: var2
    3. impure? maybe work?: addInteger var1 var2
    4. pure work-free: var3
    5. impure? maybe work?: addInteger (addInteger var1 var2) var3
  -}
  add `ap` (add `ap` varTerm 1 `ap` varTerm 2) `ap` varTerm 3

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

-- Term construction: ----------------------------------------------------------

varName :: Natural -> Name
varName n = Name ("var" <> Text.pack (show n)) (Unique (fromIntegral n))

varTerm :: Natural -> Term Name DefaultUni DefaultFun ()
varTerm n = Var () (varName n)

ap :: Term name uni fun () -> Term name uni fun () -> Term name uni fun ()
ap = Apply ()

add :: Term Name DefaultUni DefaultFun ()
add = Builtin () AddInteger
