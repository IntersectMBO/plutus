{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}

module Recursion.Spec where

import PlutusTx.Prelude
import Test.Tasty.Extras

import PlutusTx.Code
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Optimize.SpaceTime (peel, unroll)
import PlutusTx.Test
import PlutusTx.TH (compile)

tests :: TestNested
tests =
  testNested "Recursion"
    . pure
    $ testNestedGhc
      [ -- length function implemented using direct recursion
        goldenUPlcReadable
          "length-direct"
          compiledLengthDirect
      , goldenEvalCekCatch
          "length-direct"
          [compiledLengthDirect `unsafeApplyCode` liftCodeDef [1 .. 10]]
      , goldenBudget
          "length-direct"
          (compiledLengthDirect `unsafeApplyCode` liftCodeDef [1 .. 10])
      , -- length function implemented using fix
        goldenUPlcReadable
          "length-fix"
          compiledLengthFix
      , goldenEvalCekCatch
          "length-fix"
          [compiledLengthFix `unsafeApplyCode` liftCodeDef [1 .. 10]]
      , goldenBudget
          "length-fix"
          (compiledLengthFix `unsafeApplyCode` liftCodeDef [1 .. 10])
      , -- length function implemented using fix
        -- with 3 steps "peeled off" before recursing
        goldenUPlcReadable
          "length-peeled"
          compiledLengthPeeled
      , goldenEvalCekCatch
          "length-peeled"
          [compiledLengthPeeled `unsafeApplyCode` liftCodeDef [1 .. 10]]
      , goldenBudget
          "length-peeled"
          (compiledLengthPeeled `unsafeApplyCode` liftCodeDef [1 .. 10])
      , -- length function implemented using fix
        -- with 3 steps "unrolled" per each recursive call
        goldenUPlcReadable
          "length-unrolled"
          compiledLengthUnrolled
      , goldenEvalCekCatch
          "length-unrolled"
          [compiledLengthUnrolled `unsafeApplyCode` liftCodeDef [1 .. 10]]
      , goldenBudget
          "length-unrolled"
          (compiledLengthUnrolled `unsafeApplyCode` liftCodeDef [1 .. 10])
      ]

lengthDirect :: [Integer] -> Integer
lengthDirect = \case
  [] -> 0
  _ : xs -> 1 + lengthDirect xs

lengthFix :: [Integer] -> Integer
lengthFix =
  fix \self -> \case
    [] -> 0
    _ : xs -> 1 + self xs

lengthPeeled :: [Integer] -> Integer
lengthPeeled =
  $$( peel 3 \self ->
        [||
        \case
          [] -> 0
          _ : xs -> 1 + $$self xs
        ||]
    )

lengthUnrolled :: [Integer] -> Integer
lengthUnrolled =
  $$( unroll 3 \self ->
        [||
        \case
          [] -> 0
          _ : xs -> 1 + $$self xs
        ||]
    )

compiledLengthDirect :: CompiledCode ([Integer] -> Integer)
compiledLengthDirect = $$(compile [||lengthDirect||])

compiledLengthFix :: CompiledCode ([Integer] -> Integer)
compiledLengthFix = $$(compile [||lengthFix||])

compiledLengthPeeled :: CompiledCode ([Integer] -> Integer)
compiledLengthPeeled = $$(compile [||lengthPeeled||])

compiledLengthUnrolled :: CompiledCode ([Integer] -> Integer)
compiledLengthUnrolled = $$(compile [||lengthUnrolled||])
