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
import PlutusTx.Optimize.SpaceTime (peel)
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test
import PlutusTx.TH (compile)

tests :: TestNested
tests =
  testNested "Recursion" . pure $
    testNestedGhc
      [ goldenUPlcReadable "length-direct" compiledLengthDirect
      , goldenEvalCekCatch
          "length-direct"
          [compiledLengthDirect `unsafeApplyCode` liftCodeDef [1..10]]
      , goldenBudget
          "length-direct"
          (compiledLengthDirect `unsafeApplyCode` liftCodeDef [1..10])
      , goldenUPlcReadable "length-fix" compiledLengthFix
      , goldenEvalCekCatch
          "length-fix"
          [compiledLengthFix `unsafeApplyCode` liftCodeDef [1..10]]
      , goldenBudget
          "length-fix"
          (compiledLengthFix `unsafeApplyCode` liftCodeDef [1..10])
      , goldenUPlcReadable "length-peeled" compiledLengthPeeled
      , goldenEvalCekCatch
          "length-peeled"
          [compiledLengthPeeled `unsafeApplyCode` liftCodeDef [1..10]]
      , goldenBudget
          "length-peeled"
          (compiledLengthPeeled `unsafeApplyCode` liftCodeDef [1..10])
      ]

lengthDirect :: [Integer] -> Integer
lengthDirect = \case
  []       -> 0
  (_ : xs) -> 1 PlutusTx.+ lengthDirect xs

lengthFix :: [Integer] -> Integer
lengthFix =
  fix
    ( \f -> \case
        []       -> 0
        (_ : xs) -> 1 PlutusTx.+ f xs
    )

lengthPeeled :: [Integer] -> Integer
lengthPeeled = $$(peel 3 (\f -> [|| \case [] -> 0; (_ : xs) -> 1 PlutusTx.+ $$f xs ||]))

compiledLengthDirect :: CompiledCode ([Integer] -> Integer)
compiledLengthDirect = $$(compile [||lengthDirect||])

compiledLengthFix :: CompiledCode ([Integer] -> Integer)
compiledLengthFix = $$(compile [||lengthFix||])

compiledLengthPeeled :: CompiledCode ([Integer] -> Integer)
compiledLengthPeeled = $$(compile [||lengthPeeled||])
