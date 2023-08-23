module NamesSpec
    ( names
    ) where

import PlutusPrelude

import PlutusIR.Generators.AST
import PlutusIR.Mark
import PlutusIR.Transform.Beta
import PlutusIR.Transform.CaseReduce
import PlutusIR.Transform.CommuteFnWithConst
import PlutusIR.Transform.DeadCode
import PlutusIR.Transform.EvaluateBuiltins
import PlutusIR.Transform.Inline.Inline qualified as Inline
import PlutusIR.Transform.KnownCon
import PlutusIR.Transform.LetFloatIn qualified as In
import PlutusIR.Transform.LetMerge
import PlutusIR.Transform.NonStrict
import PlutusIR.Transform.RecSplit
import PlutusIR.Transform.Rename
import PlutusIR.Transform.ThunkRecursions
import PlutusIR.Transform.Unwrap

import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Rename
import PlutusCore.Test

import Test.Tasty

-- See Note [Scoping tests API].
names :: TestTree
names = testGroup "names"
    [ test_scopingGood "beta-reduction" genTerm BindingRemovalNotOk PrerenameYes $
        pure . beta
    , test_scopingGood "case-of-known-constructor" genTerm BindingRemovalNotOk PrerenameYes $
        pure . caseReduce
    , test_scopingGood "'commuteDefaultFun'" genTerm BindingRemovalNotOk PrerenameYes $
        pure . commuteDefaultFun
    , -- We say that it's fine to remove bindings, because they never actually get removed,
      -- because the scope checking machinery doesn't create unused bindings, every binding
      -- gets referenced at some point at least once (usually very close to the binding site).
      -- So this test doesn't really test much.
      test_scopingGood "dead code elimination" genTerm BindingRemovalNotOk PrerenameNo $
        removeDeadBindings def
    , test_scopingGood "constant folding" genTerm BindingRemovalNotOk PrerenameYes $
        pure . evaluateBuiltins False def defaultBuiltinCostModel
    , -- At the moment the inliner does not preserve global uniqueness (contrary to what it
      -- promises) due to the lack of marking in it (or initial renaming of the entire program,
      -- which would perform marking too).
      test_scopingBad "inlining" genTerm BindingRemovalOk PrerenameYes $
        Inline.inline mempty def
    , test_scopingGood "match-against-known-constructor" genTerm BindingRemovalNotOk PrerenameNo $
        knownCon
    , test_scopingGood "floating bindings inwards" genTerm BindingRemovalNotOk PrerenameNo $
        In.floatTerm def True
    -- Can't test 'Out.floatTerm', because it requires the type of annotations to implement
    -- 'Semigroup' and it's not clear what that means for 'NameAnn'.
    , test_scopingGood "merging lets" genTerm BindingRemovalNotOk PrerenameYes $
        pure . letMerge
    , -- The pass breaks global uniqueness, but it's not clear whether this is by design or not.
      test_scopingBad "compilation of non-strict bindings" genTerm BindingRemovalOk PrerenameYes $
        compileNonStrictBindings True
    , test_scopingGood "match-against-known-constructor" genTerm BindingRemovalNotOk PrerenameYes $
        pure . recSplit
    , test_scopingGood "renaming" genProgram BindingRemovalNotOk PrerenameNo $
        rename
    , test_scopingSpoilRenamer genProgram markNonFreshProgram
        renameProgramM
    -- Can't test substitution procedures at the moment, because that requires generating
    -- functions.
    , -- The pass breals global uniqueness by design.
      test_scopingBad "thunking recursions" genTerm BindingRemovalOk PrerenameYes $
        pure . thunkRecursions def
    , test_scopingGood "unwrap-wrap cancelling" genTerm BindingRemovalNotOk PrerenameYes $
        pure . unwrapCancel
    ]
