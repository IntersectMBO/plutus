{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}

module BuiltinList.Budget.Spec where

import PlutusTx.Prelude

import PlutusTx.BuiltinList ((!!))
import PlutusTx.BuiltinList qualified as List
import PlutusTx.Code (CompiledCode, unsafeApplyCode)
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Test (goldenBundle)
import PlutusTx.TH (compile)
import System.FilePath ((</>))
import Test.Tasty (TestName)
import Test.Tasty.Extras (TestNested, testNested, testNestedGhc)

tests :: TestNested
tests = testNested ("BuiltinList" </> "Budget") . pure $ do
  testNestedGhc
    [ goldenBundleBuiltinList "map" map
    , goldenBundleBuiltinList "elem" elem
    , goldenBundleBuiltinList "find" find
    , goldenBundleBuiltinList "any" any
    , goldenBundleBuiltinList "all" all
    , goldenBundleBuiltinList "index" index
    , goldenBundleBuiltinList "index-out-of-bounds" indexOutOfBounds
    ]

goldenBundleBuiltinList
  :: TestName
  -> CompiledCode (BuiltinList Integer -> a)
  -> TestNested
goldenBundleBuiltinList label code =
  let ints :: [Integer] = [1 .. 10]
      applied = unsafeApplyCode code (liftCodeDef (toBuiltin ints))
   in goldenBundle label code applied

map :: CompiledCode (BuiltinList Integer -> BuiltinList Integer)
map = $$(compile [||List.map (+ 1)||])

elem :: CompiledCode (BuiltinList Integer -> (Bool, Bool))
elem = $$(compile [||\xs -> (List.elem 8 xs, List.elem 12 xs)||])

find :: CompiledCode (BuiltinList Integer -> (Maybe Integer, Maybe Integer))
find = $$(compile [||\xs -> (List.find (>= 8) xs, List.find (>= 12) xs)||])

any :: CompiledCode (BuiltinList Integer -> (Bool, Bool))
any = $$(compile [||\xs -> (List.any (>= 8) xs, List.any (>= 12) xs)||])

all :: CompiledCode (BuiltinList Integer -> (Bool, Bool))
all = $$(compile [||\xs -> (List.all (>= 8) xs, List.all (>= 0) xs)||])

index :: CompiledCode (BuiltinList Integer -> Integer)
index = $$(compile [||(!! 5)||])

indexOutOfBounds :: CompiledCode (BuiltinList Integer -> Integer)
indexOutOfBounds = $$(compile [||(!! 20)||])
