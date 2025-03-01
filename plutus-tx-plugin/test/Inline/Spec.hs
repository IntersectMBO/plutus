{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}

module Inline.Spec where

import System.FilePath

import Test.Tasty.Extras

import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Optimize.Inline (inline)
import PlutusTx.Test (goldenBudget, goldenEvalCekCatch, goldenPirReadable, goldenUPlcReadable)
import PlutusTx.TH (compile)

tests :: TestNested
tests =
  testNested ("AsData" </> "Budget") . pure $
    testNestedGhc
      [ goldenPirReadable "noinline" notInlined
      , goldenUPlcReadable "noinline" notInlined
      , goldenEvalCekCatch
          "noinline"
          [ notInlined
              `unsafeApplyCode` liftCodeDef 1
              `unsafeApplyCode` liftCodeDef 2
              `unsafeApplyCode` liftCodeDef 3
          ]
      , goldenBudget
          "noinline"
          ( notInlined
              `unsafeApplyCode` liftCodeDef 1
              `unsafeApplyCode` liftCodeDef 2
              `unsafeApplyCode` liftCodeDef 3
          )
      , goldenPirReadable "inline-once" inlineOnce
      , goldenUPlcReadable "inline-once" inlineOnce
      , goldenEvalCekCatch
          "inline-once"
          [ inlineOnce
              `unsafeApplyCode` liftCodeDef 1
              `unsafeApplyCode` liftCodeDef 2
              `unsafeApplyCode` liftCodeDef 3
          ]
      , goldenBudget
          "inline-once"
          ( inlineOnce
              `unsafeApplyCode` liftCodeDef 1
              `unsafeApplyCode` liftCodeDef 2
              `unsafeApplyCode` liftCodeDef 3
          )
      , goldenPirReadable "inline-once-applied" inlineOnceApplied
      , goldenUPlcReadable "inline-once-applied" inlineOnceApplied
      , goldenEvalCekCatch
          "inline-once-applied"
          [ inlineOnceApplied
              `unsafeApplyCode` liftCodeDef 1
              `unsafeApplyCode` liftCodeDef 2
              `unsafeApplyCode` liftCodeDef 3
          ]
      , goldenBudget
          "inline-once-applied"
          ( inlineOnceApplied
              `unsafeApplyCode` liftCodeDef 1
              `unsafeApplyCode` liftCodeDef 2
              `unsafeApplyCode` liftCodeDef 3
          )
      , goldenPirReadable "inline-twice" inlineTwice
      , goldenUPlcReadable "inline-twice" inlineTwice
      , goldenEvalCekCatch
          "inline-twice"
          [ inlineTwice
              `unsafeApplyCode` liftCodeDef 1
              `unsafeApplyCode` liftCodeDef 2
              `unsafeApplyCode` liftCodeDef 3
          ]
      , goldenBudget
          "inline-twice"
          ( inlineTwice
              `unsafeApplyCode` liftCodeDef 1
              `unsafeApplyCode` liftCodeDef 2
              `unsafeApplyCode` liftCodeDef 3
          )
      , goldenPirReadable "recursive" recursive
      , goldenUPlcReadable "recursive" recursive
      , goldenPirReadable "inlineLocalOnce" compiledInlineLocalOnce
      , goldenUPlcReadable "inlineLocalOnce" compiledInlineLocalOnce
      , goldenEvalCekCatch
          "inlineLocalOnce"
          [compiledInlineLocalOnce `unsafeApplyCode` liftCodeDef 2]
      ]

double :: Integer -> Integer
double x = x `PlutusTx.addInteger` x
{-# INLINEABLE double #-}

factorial :: Integer -> Integer
factorial x
  | x `PlutusTx.equalsInteger` 0 = 1
  | otherwise = x `PlutusTx.multiplyInteger` factorial (x `PlutusTx.subtractInteger` 1)
{-# INLINEABLE factorial #-}

{-| This test case verifies that `inline` can inline local bindings
(like `square`).

The third usage of `square` is inlined in PIR, but not in UPLC, since
in UPLC the inlining is reversed by CSE.
-}
inlineLocalOnce :: Integer -> Integer
inlineLocalOnce x = square `PlutusTx.addInteger` square `PlutusTx.addInteger` inline square
  where
    !square = x `PlutusTx.multiplyInteger` x
{-# INLINEABLE inlineLocalOnce #-}

notInlined :: CompiledCode (Integer -> Integer -> Integer -> Integer)
notInlined =
  $$( compile
        [||
        \x y z ->
          double x
            `PlutusTx.multiplyInteger` double y
            `PlutusTx.multiplyInteger` double z
        ||]
    )

inlineOnce :: CompiledCode (Integer -> Integer -> Integer -> Integer)
inlineOnce =
  $$( compile
        [||
        \x y z ->
          double x
            `PlutusTx.multiplyInteger` double y
            `PlutusTx.multiplyInteger` inline double z
        ||]
    )

inlineOnceApplied :: CompiledCode (Integer -> Integer -> Integer -> Integer)
inlineOnceApplied =
  $$( compile
        [||
        \x y z ->
          double x
            `PlutusTx.multiplyInteger` double y
            `PlutusTx.multiplyInteger` inline (double z)
        ||]
    )

-- This effectively inlines all 3 occurrences of `double`, since the remaining occurrence
-- is unconditionally inlined.
inlineTwice :: CompiledCode (Integer -> Integer -> Integer -> Integer)
inlineTwice =
  $$( compile
        [||
        \x y z ->
          inline double x
            `PlutusTx.multiplyInteger` double y
            `PlutusTx.multiplyInteger` inline double z
        ||]
    )

-- Recursive functions should not be inlined.
recursive :: CompiledCode (Integer -> Integer -> Integer -> Integer)
recursive =
  $$( compile
        [||
        \x y z ->
          factorial x
            `PlutusTx.multiplyInteger` factorial y
            `PlutusTx.multiplyInteger` inline factorial z
        ||]
    )

compiledInlineLocalOnce :: CompiledCode (Integer -> Integer)
compiledInlineLocalOnce = $$(compile [||inlineLocalOnce||])
