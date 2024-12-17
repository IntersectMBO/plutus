{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

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
        , goldenPirReadable "compiledLengthArray" compiledLengthArray
        , goldenUPlcReadable "compiledLengthArray" compiledLengthArray
        , goldenUEval "compiledLengthArray" [compiledLengthArray]
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

compiledLengthArray :: CompiledCode BuiltinInteger
compiledLengthArray =
  $$(compile [||lengthOfArray||]) `unsafeApplyCode` compiledListToArray

compiledIndexArray :: CompiledCode BuiltinData
compiledIndexArray =
  $$(compile [||indexArray||])
    `unsafeApplyCode` compiledListToArray
    `unsafeApplyCode` liftCodeDef 2
