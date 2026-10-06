{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Example.Ual.Recursive.FormalSpec (annotations) where

import Example.Ual.Recursive.OnChain (Tree, mirrorData, treeValidator)
import PlutusTx.Prelude (BuiltinData, BuiltinUnit)
import PlutusTx.Ual (ModuleUal)
import PlutusTx.Ual.TH (ualModule)

{-@ ONCHAIN [kind: script] [version: PlutusV3] [steps: 3000, semantics: E]
  treeValidator :: Tree -> BuiltinData -> BuiltinUnit
@-}
{-@ ONCHAIN [kind: function] [version: PlutusV3] [steps: 3000, semantics: E]
  mirrorData :: Tree -> Tree
@-}
{-@ PREDICATE
  def leaf (n : Integer) : Data := Data.Constr 0 [Data.I n]
  def branch (l r : Data) : Data := Data.Constr 1 [l, r]
@-}
{-@ PROPERTY [scope: treeValidator] leaf_seven
  "A leaf parameter is accepted exactly when it contains seven."
  : ∀ (n : Integer) (ctx : Data), isSuccessful (treeValidator (leaf n) ctx) ↔ n = 7
@-}
{-@ PROPERTY [scope: treeValidator] nested_sum
  "The recursive parameter is decoded and all three leaves contribute."
  : ∀ (a b c : Integer) (ctx : Data),
      isSuccessful (treeValidator (branch (leaf a) (branch (leaf b) (leaf c))) ctx) ↔ a + (b + c) = 7
@-}
{-@ PROPERTY [scope: mirrorData] nested_mirror
  "The compiled helper reverses the recursive branches and returns Data."
  : ∀ (a b c : Integer),
      mirrorData_returns (branch (leaf a) (branch (leaf b) (leaf c))) (branch (branch (leaf c) (leaf b)) (leaf a))
@-}
{-@ PROPERTY [scope: mirrorData] malformed_tree
  "A bare integer is rejected, despite crossing the boundary as raw Data."
  : ∀ (n : Integer), isUnsuccessful (mirrorData (Data.I n))
@-}
annotations :: ModuleUal
annotations = $(ualModule)
