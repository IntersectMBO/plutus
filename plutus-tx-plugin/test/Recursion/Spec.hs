{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ViewPatterns          #-}

{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}

module Recursion.Spec where

import Test.Tasty.Extras

import PlutusTx.Code
import PlutusTx.Function (fix)
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test
import PlutusTx.TH (compile)

tests :: TestNested
tests =
  testNested "Recursion" . pure $
    testNestedGhc
      [ goldenUPlcReadable "length-direct" compiledLengthDirect
      , goldenPirReadable "length-direct" compiledLengthDirect
      , goldenEvalCekCatch
          "length-direct"
          [compiledLengthDirect `unsafeApplyCode` liftCodeDef [1, 2, 3]]
      , goldenBudget
          "length-direct"
          (compiledLengthDirect `unsafeApplyCode` liftCodeDef [1, 2, 3])
      , goldenUPlcReadable "length-fix" compiledLengthFix
      , goldenPirReadable "length-fix" compiledLengthFix
      , goldenEvalCekCatch
          "length-fix"
          [compiledLengthFix `unsafeApplyCode` liftCodeDef [1, 2, 3]]
      , goldenBudget
          "length-fix"
          (compiledLengthFix `unsafeApplyCode` liftCodeDef [1, 2, 3])
      ]

lengthDirect :: [Integer] -> Integer
lengthDirect xs = case xs of
  []       -> 0
  (_ : ys) -> 1 PlutusTx.+ lengthDirect ys

lengthFix :: [Integer] -> Integer
lengthFix =
  fix
    ( \f xs -> case xs of
        []       -> 0
        (_ : ys) -> 1 PlutusTx.+ f ys
    )

compiledLengthDirect :: CompiledCode ([Integer] -> Integer)
compiledLengthDirect = $$(compile [||lengthDirect||])

compiledLengthFix :: CompiledCode ([Integer] -> Integer)
compiledLengthFix = $$(compile [||lengthFix||])
