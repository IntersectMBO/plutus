{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Scoping.Spec where

import UntypedPlutusCore
import UntypedPlutusCore.Generators.Hedgehog.AST (genProgram, genTerm, mangleNames, runAstGen)
import UntypedPlutusCore.Mark
import UntypedPlutusCore.Rename.Internal
import UntypedPlutusCore.Transform.CaseReduce (caseReduce)
import UntypedPlutusCore.Transform.Cse (cse)
import UntypedPlutusCore.Transform.FloatDelay (floatDelay)
import UntypedPlutusCore.Transform.ForceDelay (forceDelay)
import UntypedPlutusCore.Transform.Inline (inline)

import PlutusCore.Generators.Hedgehog.Utils
import PlutusCore.Quote
import PlutusCore.Rename
import PlutusCore.Test qualified as T

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Test.Tasty
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit

test_mangle :: TestTree
test_mangle =
  testPropertyNamed "equality does not survive mangling" "equality_mangling" $
      withDiscards 1000000 . T.mapTestLimitAtLeast 300 (`div` 3) . property $ do
          (term, termMangled) <- forAll . runAstGen . Gen.justT $ do
            term <- genTerm
            mayTermMang <- mangleNames term
            pure $ (,) term <$> mayTermMang
          term /== termMangled
          termMangled /== term

-- | Test equality of a program and its renamed version, given a renamer.
prop_equalityFor
  :: program ~ Program Name DefaultUni DefaultFun ()
  => (program -> Quote program)
  -> Property
prop_equalityFor ren = property $ do
  prog <- forAllPretty $ runAstGen genProgram
  let progRen = runQuote $ ren prog
  progRen === prog
  prog === progRen

test_equalityRename :: TestTree
test_equalityRename =
  testPropertyNamed "equality survives renaming" "equality_renaming" $
    prop_equalityFor rename

test_equalityBrokenRename :: TestTree
test_equalityBrokenRename =
  testCase "equality does not survive wrong renaming" $
    T.checkFails . prop_equalityFor $
      T.brokenRename markNonFreshProgram renameProgramM

test_equalityNoMarkRename :: TestTree
test_equalityNoMarkRename =
  testCase "equality does not survive renaming without marking" $
    T.checkFails . prop_equalityFor $
      T.noMarkRename renameProgramM

-- See Note [Scoping tests API].
test_names :: TestTree
test_names = testGroup "names"
    [ T.test_scopingGood "renaming" (genProgram @DefaultFun) T.BindingRemovalNotOk T.PrerenameNo
        rename
    , T.test_scopingSpoilRenamer (genProgram @DefaultFun) markNonFreshProgram
        renameProgramM
    -- We don't test case-of-case, because it duplicates binders and we don't support that in the
    -- scoping tests machinery.
    , T.test_scopingGood "case-of-known-constructor"
        (genTerm @DefaultFun)
        T.BindingRemovalOk  -- COKC removes branches, which may (and likely do) contain bindings.
        T.PrerenameYes
        (evalSimplifierT . caseReduce)
    , -- CSE creates entirely new names, which isn't supported by the scoping check machinery.
      T.test_scopingBad "cse"
        (genTerm @DefaultFun)
        T.BindingRemovalOk
        T.PrerenameYes
        (evalSimplifierT . cse maxBound)
    , T.test_scopingGood "float-delay"
        (genTerm @DefaultFun)
        T.BindingRemovalNotOk
        T.PrerenameNo
        (evalSimplifierT . floatDelay)
    , T.test_scopingGood "force-delay"
        (genTerm @DefaultFun)
        T.BindingRemovalNotOk
        T.PrerenameYes
        (evalSimplifierT . forceDelay maxBound)
    , T.test_scopingGood "inline"
        (genTerm @DefaultFun)
        T.BindingRemovalOk
        T.PrerenameYes
        (evalSimplifierT .
          inline 0
            True
            (_soPreserveLogging defaultSimplifyOpts)
            (_soInlineHints defaultSimplifyOpts)
            maxBound )
    , test_mangle
    , test_equalityRename
    , test_equalityBrokenRename
    , test_equalityNoMarkRename
    ]
