module PlutusIR.Scoping.Tests where

import PlutusPrelude

import PlutusIR.Generators.AST
import PlutusIR.Mark
import PlutusIR.Transform.Beta
import PlutusIR.Transform.CaseReduce
import PlutusIR.Transform.DeadCode
import PlutusIR.Transform.EvaluateBuiltins
import PlutusIR.Transform.Inline.Inline qualified as Inline
import PlutusIR.Transform.KnownCon
import PlutusIR.Transform.LetFloatIn qualified as In
import PlutusIR.Transform.LetMerge
import PlutusIR.Transform.NonStrict
import PlutusIR.Transform.RecSplit
import PlutusIR.Transform.Rename
import PlutusIR.Transform.RewriteRules.CommuteFnWithConst
import PlutusIR.Transform.ThunkRecursions
import PlutusIR.Transform.Unwrap

import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Rename
import PlutusCore.Test qualified as T

import Test.Tasty

-- See Note [Scoping tests API].
test_names :: TestTree
test_names =
  testGroup
    "names"
    [ T.test_scopingGood "beta-reduction" genTerm T.BindingRemovalNotOk T.PrerenameYes $
        pure . beta
    , T.test_scopingGood "case-of-known-constructor" genTerm T.BindingRemovalOk T.PrerenameYes $
        pure . caseReduce
    , T.test_scopingGood "commuteFnWithConst" genTerm T.BindingRemovalNotOk T.PrerenameYes $
        pure . commuteFnWithConst
    , -- We say that it's fine to remove bindings, because they never actually get removed,
      -- because the scope checking machinery doesn't create unused bindings, every binding
      -- gets referenced at some point at least once (usually very close to the binding site).
      -- So this test doesn't really test much.
      T.test_scopingGood "dead code elimination" genTerm T.BindingRemovalNotOk T.PrerenameYes $
        removeDeadBindings def
    , T.test_scopingGood "constant folding" genTerm T.BindingRemovalNotOk T.PrerenameYes $
        pure . evaluateBuiltins False def defaultBuiltinCostModelForTesting
    , -- At the moment the inliner does not preserve global uniqueness (contrary to what it
      -- promises) due to the lack of marking in it (or initial renaming of the entire program,
      -- which would perform marking too).
      T.test_scopingBad "inlining" genTerm T.BindingRemovalOk T.PrerenameYes $
        Inline.inline 0 True def def
    , T.test_scopingGood
        "match-against-known-constructor"
        genTerm
        T.BindingRemovalNotOk
        T.PrerenameYes
        $ (pure . knownCon)
    , T.test_scopingGood "floating bindings inwards" genTerm T.BindingRemovalNotOk T.PrerenameYes $
        (pure . In.floatTerm def True)
    , -- Can't test 'Out.floatTerm', because it requires the type of annotations to implement
      -- 'Semigroup' and it's not clear what that means for 'NameAnn'.
      T.test_scopingGood "merging lets" genTerm T.BindingRemovalNotOk T.PrerenameYes $
        pure . letMerge
    , -- The pass breaks global uniqueness, but it's not clear whether this is by design or not.
      T.test_scopingBad
        "compilation of non-strict bindings"
        genTerm
        T.BindingRemovalOk
        T.PrerenameYes
        $ compileNonStrictBindings True
    , T.test_scopingGood
        "match-against-known-constructor"
        genTerm
        T.BindingRemovalNotOk
        T.PrerenameYes
        $ pure . recSplit
    , T.test_scopingGood "renaming" genProgram T.BindingRemovalNotOk T.PrerenameNo $
        rename
    , T.test_scopingSpoilRenamer
        genProgram
        markNonFreshProgram
        renameProgramM
    , -- Can't test substitution procedures at the moment, because that requires generating
      -- functions.
      -- The pass breals global uniqueness by design.
      T.test_scopingBad "thunking recursions" genTerm T.BindingRemovalOk T.PrerenameYes $
        pure . thunkRecursions def
    , T.test_scopingGood "unwrap-wrap cancelling" genTerm T.BindingRemovalNotOk T.PrerenameYes $
        pure . unwrapCancel
    ]
