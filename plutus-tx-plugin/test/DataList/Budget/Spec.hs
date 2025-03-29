{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

module DataList.Budget.Spec where

import Prelude hiding (any, elem, filter, length)
import System.FilePath
import Test.Tasty.Extras

import PlutusTx.Code
import PlutusTx.Data.List qualified as L
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Prelude qualified as P
import PlutusTx.Test
import PlutusTx.TH (compile)

tests :: TestNested
tests =
  testNested ("List" </> "Budget") . pure $
    testNestedGhc
      [ goldenPirReadable "length" length
      , goldenUPlcReadable "length" length
      , goldenEvalCekCatch "length" [length `unsafeApplyCode` l]
      , goldenBudget "length" (length `unsafeApplyCode` l)
      , goldenPirReadable "filter" filter
      , goldenUPlcReadable "filter" filter
      , goldenEvalCekCatch "filter" [filter `unsafeApplyCode` l]
      , goldenBudget "filter" (filter `unsafeApplyCode` l)
      , goldenPirReadable "any" any
      , goldenUPlcReadable "any" any
      , goldenEvalCekCatch "any" [any `unsafeApplyCode` l]
      , goldenBudget "any" (any `unsafeApplyCode` l)
      , goldenPirReadable "elem" elem
      , goldenUPlcReadable "elem" elem
      , goldenEvalCekCatch "elem" [elem `unsafeApplyCode` l]
      , goldenBudget "elem" (elem `unsafeApplyCode` l)
      , goldenPirReadable "partition" partition
      , goldenUPlcReadable "partition" partition
      , goldenEvalCekCatch "partition" [partition `unsafeApplyCode` l]
      , goldenBudget "partition" (partition `unsafeApplyCode` l)
      , goldenPirReadable "makeList" makeList
      , goldenUPlcReadable "makeList" makeList
      , goldenEvalCekCatch
          "makeList"
          [ makeList
              `unsafeApplyCode` liftCodeDef 1
              `unsafeApplyCode` liftCodeDef 2
              `unsafeApplyCode` liftCodeDef 3
          ]
      , goldenBudget
          "makeList"
          ( makeList
              `unsafeApplyCode` liftCodeDef 1
              `unsafeApplyCode` liftCodeDef 2
              `unsafeApplyCode` liftCodeDef 3
          )
      ]

length :: CompiledCode (L.List Integer -> Integer)
length =
  $$(compile [||L.length||])

filter :: CompiledCode (L.List Integer -> L.List Integer)
filter =
  $$(compile [||L.filter (P.>= 8)||])

any :: CompiledCode (L.List Integer -> Bool)
any =
  $$(compile [||L.any (P.>= 8)||])

elem :: CompiledCode (L.List Integer -> Bool)
elem =
  $$(compile [||L.elem 8||])

partition :: CompiledCode (L.List Integer -> (L.List Integer, L.List Integer))
partition =
  $$(compile [||L.partition (P.>= 8)||])

makeList :: CompiledCode (Integer -> Integer -> Integer -> L.List Integer)
makeList =
  $$( compile
        [||
        \x y z ->
          L.cons x . L.cons y . L.cons z $ P.mempty
        ||]
    )

l :: CompiledCode (L.List Integer)
l = liftCodeDef (L.fromSOP [1 .. 10])
