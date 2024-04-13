-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}

module Map.Spec where

import Test.Tasty.Extras

import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.DataMap qualified as Map
import PlutusTx.IsData qualified as PlutusTx
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Test
import PlutusTx.TH (compile)

tests :: TestNested
tests =
  testNestedGhc
    "Budget"
    [ goldenPirReadable "all1" all1
    , goldenUPlcReadable "all1" all1
    , goldenEvalCekCatch "all1" [all1 `unsafeApplyCode` liftCodeDef arg]
    , goldenBudget "all1" $ all1 `unsafeApplyCode` liftCodeDef arg

    , goldenPirReadable "all2" all2
    , goldenUPlcReadable "all2" all2
    , goldenEvalCekCatch "all2" [all2 `unsafeApplyCode` liftCodeDef arg]
    , goldenBudget "all2" $ all2 `unsafeApplyCode` liftCodeDef arg
    ]

all1 :: CompiledCode (PlutusTx.BuiltinData -> Bool)
all1 =
  $$( compile
        [||
        \inp ->
          let datamap :: Map.Map Integer Integer
              datamap = PlutusTx.unsafeFromBuiltinData inp
           in Map.all (`PlutusTx.lessThanInteger` 10) datamap
        ||]
    )

all2 :: CompiledCode (PlutusTx.BuiltinData -> Bool)
all2 =
  $$( compile
        [||
        \inp ->
          let datamap :: Map.Map Integer Integer
              datamap = PlutusTx.unsafeFromBuiltinData inp
           in Map.all2 (`PlutusTx.lessThanInteger` 10) datamap
        ||]
    )

arg :: PlutusTx.BuiltinData
arg = PlutusTx.toBuiltinData (Map.singleton 1 5 :: Map.Map Integer Integer)
