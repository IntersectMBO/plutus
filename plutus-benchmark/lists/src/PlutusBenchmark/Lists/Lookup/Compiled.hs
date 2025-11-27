{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

module PlutusBenchmark.Lists.Lookup.Compiled where

import PlutusTx qualified as Tx
import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Lift ()
import PlutusTx.List qualified as L
import PlutusTx.Plugin ()
import PlutusTx.Prelude qualified as P

{-
A simple matching workload:
- Two lists of indices (rather than a list of pairs to avoid having to put pairs in a
builtin list)
- Two lists of numbers

The task is to go through the indices in sync, taking the corresponding number from each
list, and adding them all.

This is naturally quadratic for a linked-list.
-}
type Workload f = (f Integer, f Integer, f Integer, f Integer)

workloadOfSize :: Integer -> Workload []
workloadOfSize sz =
  let
    lixs = [0 .. (sz - 1)]
    rixs = reverse lixs
    ls = take (fromIntegral sz) [1, 3 ..]
    rs = take (fromIntegral sz) [1, 2 ..]
   in
    (lixs, rixs, ls, rs)

workloadLToBl :: Workload [] -> Workload BI.BuiltinList
workloadLToBl (lixs, rixs, ls, rs) =
  (BI.BuiltinList lixs, BI.BuiltinList rixs, BI.BuiltinList ls, BI.BuiltinList rs)

matchWithLists :: Workload [] -> Integer
matchWithLists (lixs, rixs, ls, rs) = go lixs rixs 0
  where
    go (lix : lrest) (rix : rrest) acc =
      go lrest rrest ((ls L.!! lix) `B.addInteger` (rs L.!! rix) `B.addInteger` acc)
    go _ _ acc = acc

mkMatchWithListsCode :: Workload [] -> Tx.CompiledCode Integer
mkMatchWithListsCode l = $$(Tx.compile [||matchWithLists||]) `Tx.unsafeApplyCode` Tx.liftCodeDef l

matchWithBuiltinLists :: Workload BI.BuiltinList -> Integer
matchWithBuiltinLists (lixs, rixs, ls, rs) = go lixs rixs 0
  where
    go ltodo rtodo acc =
      B.matchList'
        ltodo
        acc
        ( \lix lrest ->
            B.matchList'
              rtodo
              acc
              ( \rix rrest ->
                  go
                    lrest
                    rrest
                    ((ls !! lix) `B.addInteger` (rs !! rix) `B.addInteger` acc)
              )
        )
    l !! ix =
      B.matchList'
        l
        (\() -> P.traceError "empty list")
        (\h t -> \() -> if ix P.== 0 then h else t !! (ix `B.subtractInteger` 1))
        ()

mkMatchWithBuiltinListsCode :: Workload [] -> Tx.CompiledCode Integer
mkMatchWithBuiltinListsCode l =
  $$(Tx.compile [||matchWithBuiltinLists||]) `Tx.unsafeApplyCode` Tx.liftCodeDef (workloadLToBl l)
