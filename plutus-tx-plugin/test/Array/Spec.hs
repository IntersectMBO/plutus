{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-optimize #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-simplifier-beta #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-simplifier-evaluate-builtins #-}

module Array.Spec where

import PlutusCore.Test (goldenUEval)
import PlutusTx
import PlutusTx.Builtins.Internal
import PlutusTx.Test (goldenPirReadable, goldenUPlcReadable)
import Test.Tasty.Extras

smokeTests :: TestNested
smokeTests =
  testNested
    "Array"
    [ testNestedGhc
        [ goldenPirReadable "compiledListToArray" compiledListToArray
        , goldenUPlcReadable "compiledListToArray" compiledListToArray
        , goldenUEval "compiledListToArray" [compiledListToArray]
        , goldenPirReadable "compiledLengthOfArray" compiledLengthOfArray
        , goldenUPlcReadable "compiledLengthOfArray" compiledLengthOfArray
        , goldenUEval "compiledLengthOfArray" [compiledLengthOfArray]
        , goldenPirReadable "compiledIndexArray" compiledIndexArray
        , goldenUPlcReadable "compiledIndexArray" compiledIndexArray
        , goldenUEval "compiledIndexArray" [compiledIndexArray]
        ]
    ]

compiledListToArray :: CompiledCode (BuiltinArray BuiltinData)
compiledListToArray =
  $$( compile
        [||
        listToArray
          ( mkCons
              (mkI 1)
              ( mkCons
                  (mkI 2)
                  ( mkCons
                      (mkI 3)
                      (mkNilData unitval)
                  )
              )
          )
        ||]
    )

compiledLengthOfArray :: CompiledCode BuiltinInteger
compiledLengthOfArray =
  $$(compile [||lengthOfArray||]) `unsafeApplyCode` compiledListToArray

compiledIndexArray :: CompiledCode BuiltinData
compiledIndexArray =
  $$(compile [||indexArray||])
    `unsafeApplyCode` compiledListToArray
    `unsafeApplyCode` liftCodeDef 2
