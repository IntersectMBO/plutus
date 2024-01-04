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
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}

module Map.Spec where

import Test.Tasty.Extras

import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.DataMap qualified as Map
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Show qualified as PlutusTx
import PlutusTx.Test
import PlutusTx.TH (compile)

tests :: TestNested
tests =
  testNestedGhc
    "Budget"
    [ goldenPirReadable "map1" map1
    , goldenUPlcReadable "map1" map1
    , goldenEvalCekCatch "map1" $ [map1 `unsafeApplyCode` (liftCodeDef 100)]
    , goldenBudget "map1-budget" $ map1 `unsafeApplyCode` (liftCodeDef 100)
    , goldenPirReadable "map2" map2
    , goldenUPlcReadable "map2" map2
    , goldenEvalCekCatch "map2" $ [map2 `unsafeApplyCode` (liftCodeDef 100)]
    , goldenBudget "map2-budget" $ map2 `unsafeApplyCode` (liftCodeDef 100)
    ]

map1 ::
  CompiledCode
    ( Integer ->
      ( Maybe PlutusTx.BuiltinByteString
      , Maybe PlutusTx.BuiltinByteString
      , Maybe PlutusTx.BuiltinByteString
      , Maybe PlutusTx.BuiltinByteString
      , Maybe PlutusTx.BuiltinByteString
      )
    )
map1 =
  $$( compile
        [||
        \n ->
          let m :: Map.Map Integer PlutusTx.BuiltinByteString
              m =
                foldr
                  (\i -> Map.insert (n PlutusTx.+ i) (PlutusTx.encodeUtf8 (PlutusTx.show i)))
                  (Map.singleton n "0")
                  (PlutusTx.enumFromTo 1 10)
              m' = Map.delete (n PlutusTx.+ 5) m
           in ( Map.lookup n m
              , Map.lookup (n PlutusTx.+ 5) m
              , Map.lookup (n PlutusTx.+ 10) m
              , Map.lookup (n PlutusTx.+ 20) m
              , Map.lookup (n PlutusTx.+ 5) m'
              )
        ||]
    )

map2 :: CompiledCode (Integer -> [(Integer, PlutusTx.BuiltinString)])
map2 =
  $$( compile
        [||
        \n ->
          let m1 =
                Map.unsafeFromList
                  [ (n PlutusTx.+ 1, "one")
                  , (n PlutusTx.+ 2, "two")
                  , (n PlutusTx.+ 3, "three")
                  , (n PlutusTx.+ 4, "four")
                  , (n PlutusTx.+ 5, "five")
                  ]
              m2 =
                Map.unsafeFromList
                  [ (n PlutusTx.+ 3, "THREE")
                  , (n PlutusTx.+ 4, "FOUR")
                  , (n PlutusTx.+ 6, "SIX")
                  , (n PlutusTx.+ 7, "SEVEN")
                  ]
              m = Map.unionWith PlutusTx.appendByteString m1 m2
           in PlutusTx.fmap (\(k, v) -> (k, PlutusTx.decodeUtf8 v)) (Map.toList m)
        ||]
    )
