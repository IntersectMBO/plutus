{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

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
  testNested ("DataList" </> "Budget") . pure $
    testNestedGhc
      [ goldenBundle "length" length (length `unsafeApplyCode` l)
      , goldenBundle "filter" filter (filter `unsafeApplyCode` l)
      , goldenBundle "any" any (any `unsafeApplyCode` l)
      , goldenBundle "elem" elem (elem `unsafeApplyCode` l)
      , goldenBundle "partition" partition (partition `unsafeApplyCode` l)
      , goldenBundle
          "makeList"
          makeList
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
