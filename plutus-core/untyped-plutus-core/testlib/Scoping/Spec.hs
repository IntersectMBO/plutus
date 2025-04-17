{-# LANGUAGE TypeApplications #-}

module Scoping.Spec where

import Generators (genProgram, genTerm)

import UntypedPlutusCore (_soInlineHints, defaultSimplifyOpts)
import UntypedPlutusCore.Mark
import UntypedPlutusCore.Rename.Internal
import UntypedPlutusCore.Transform.CaseOfCase (caseOfCase)
import UntypedPlutusCore.Transform.CaseReduce (caseReduce)
import UntypedPlutusCore.Transform.Cse (cse)
import UntypedPlutusCore.Transform.FloatDelay (floatDelay)
import UntypedPlutusCore.Transform.ForceDelay (forceDelay)
import UntypedPlutusCore.Transform.Inline (inline)
import UntypedPlutusCore.Transform.Simplifier (evalSimplifierT)

import PlutusCore.Default.Builtins (DefaultFun)
import PlutusCore.Rename
import PlutusCore.Test qualified as T

import Test.Tasty

-- See Note [Scoping tests API].
test_names :: TestTree
test_names = testGroup "names"
    [ T.test_scopingGood "renaming" (genProgram @DefaultFun) T.BindingRemovalNotOk T.PrerenameNo
        rename
    , T.test_scopingSpoilRenamer (genProgram @DefaultFun) markNonFreshProgram
        renameProgramM
    , T.test_scopingGood "case-of-case" (genTerm @DefaultFun) T.BindingRemovalOk T.PrerenameYes $
        evalSimplifierT . caseOfCase
    , -- COKC removes entire branches, some of which are going to contain binders, but we still use
      -- 'BindingRemovalNotOk', because the 'EstablishScoping' instance does not attempt to
      -- reference bindings from one branch in another one. We could do that, but then we'd be
      -- removing not just TODO.
      T.test_scopingGood "case-of-known-constructor"
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
        (evalSimplifierT . inline 0 True (_soInlineHints defaultSimplifyOpts) maxBound)
    ]
