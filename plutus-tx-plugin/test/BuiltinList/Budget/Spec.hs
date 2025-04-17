{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

module BuiltinList.Budget.Spec where

import Prelude hiding (all, any, elem, map)
import System.FilePath
import Test.Tasty.Extras

import PlutusTx.BuiltinList qualified as L
import PlutusTx.Builtins.HasBuiltin (HasToBuiltin (toBuiltin))
import PlutusTx.Code
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Prelude qualified as P
import PlutusTx.Test
import PlutusTx.TH (compile)

tests :: TestNested
tests =
  testNested ("BuiltinList" </> "Budget") . pure $
    testNestedGhc
      [ goldenPirReadable "map" map
      , goldenUPlcReadable "map" map
      , goldenEvalCekCatch "map" [map `unsafeApplyCode` l]
      , goldenBudget "map" (map `unsafeApplyCode` l)
      , goldenPirReadable "elem" elem
      , goldenUPlcReadable "elem" elem
      , goldenEvalCekCatch "elem" [elem `unsafeApplyCode` l]
      , goldenBudget "elem" (elem `unsafeApplyCode` l)
      , goldenPirReadable "find" find
      , goldenUPlcReadable "find" find
      , goldenEvalCekCatch "find" [find `unsafeApplyCode` l]
      , goldenBudget "find" (find `unsafeApplyCode` l)
      , goldenPirReadable "any" any
      , goldenUPlcReadable "any" any
      , goldenEvalCekCatch "any" [any `unsafeApplyCode` l]
      , goldenBudget "any" (any `unsafeApplyCode` l)
      , goldenPirReadable "all" all
      , goldenUPlcReadable "all" all
      , goldenEvalCekCatch "all" [all `unsafeApplyCode` l]
      , goldenBudget "all" (all `unsafeApplyCode` l)
      , goldenPirReadable "index" index
      , goldenUPlcReadable "index" index
      , goldenEvalCekCatch "index" [index `unsafeApplyCode` l]
      , goldenBudget "index" (index `unsafeApplyCode` l)
      ]

map :: CompiledCode (P.BuiltinList Integer -> P.BuiltinList Integer)
map = $$(compile [||L.map (P.+ 1)||])

elem :: CompiledCode (P.BuiltinList Integer -> (Bool, Bool))
elem = $$(compile [||\xs -> (L.elem 8 xs, L.elem 12 xs)||])

find :: CompiledCode (P.BuiltinList Integer -> (Maybe Integer, Maybe Integer))
find = $$(compile [||\xs -> (L.find (P.>= 8) xs, L.find (P.>= 12) xs)||])

any :: CompiledCode (P.BuiltinList Integer -> (Bool, Bool))
any = $$(compile [||\xs -> (L.any (P.>= 8) xs, L.any (P.>= 12) xs)||])

all :: CompiledCode (P.BuiltinList Integer -> (Bool, Bool))
all = $$(compile [||\xs -> (L.all (P.>= 8) xs, L.all (P.>= 0) xs)||])

index :: CompiledCode (P.BuiltinList Integer -> Integer)
index = $$(compile [|| (L.!! 5) ||])

l :: CompiledCode (P.BuiltinList Integer)
l = liftCodeDef $ toBuiltin ([1 .. 10] :: [Integer])
