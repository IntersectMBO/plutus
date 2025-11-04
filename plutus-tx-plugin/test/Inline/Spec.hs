{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

module Inline.Spec where

import System.FilePath

import Test.Tasty.Extras

import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Optimize.Inline (inline)
import PlutusTx.Test (goldenBundle, goldenPirReadable, goldenUPlcReadable)
import PlutusTx.TH (compile)

tests :: TestNested
tests =
  testNested ("AsData" </> "Budget") . pure $
    testNestedGhc
      [ goldenBundle "noinline" notInlined (applyOneTwoThree notInlined)
      , goldenBundle "inline-once" inlineOnce (applyOneTwoThree inlineOnce)
      , goldenBundle "inline-once-applied" inlineOnceApplied (applyOneTwoThree inlineOnceApplied)
      , goldenBundle "inline-twice" inlineTwice (applyOneTwoThree inlineTwice)
      , goldenPirReadable "recursive" recursive
      , goldenUPlcReadable "recursive" recursive
      , goldenBundle
          "inlineLocalOnce"
          compiledInlineLocalOnce
          (compiledInlineLocalOnce `unsafeApplyCode` liftCodeDef 2)
      , goldenPirReadable "always-inline-local" compiledAlwaysInlineLocal
      , goldenUPlcReadable "always-inline-local" compiledAlwaysInlineLocal
      ]
 where
  applyOneTwoThree f =
    f
      `unsafeApplyCode` liftCodeDef 1
      `unsafeApplyCode` liftCodeDef 2
      `unsafeApplyCode` liftCodeDef 3

double :: Integer -> Integer
double x = x `PlutusTx.addInteger` x
{-# INLINEABLE double #-}

factorial :: Integer -> Integer
factorial x
  | x `PlutusTx.equalsInteger` 0 = 1
  | otherwise = x `PlutusTx.multiplyInteger` factorial (x `PlutusTx.subtractInteger` 1)
{-# INLINEABLE factorial #-}

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

-- Use INLINE pragma on local variable `square` to make it always inlined.
-- Similar to `inlineLocalOnce`, the inlining can be seen in PIR, but is
-- reversed by CSE in UPLC.
alwaysInlineLocal :: Integer -> Integer
alwaysInlineLocal x = square `PlutusTx.addInteger` square `PlutusTx.addInteger` square
 where
  !square = x `PlutusTx.multiplyInteger` x
  {-# INLINE square #-}
{-# INLINEABLE alwaysInlineLocal #-}

compiledInlineLocalOnce :: CompiledCode (Integer -> Integer)
compiledInlineLocalOnce = $$(compile [||inlineLocalOnce||])

compiledAlwaysInlineLocal :: CompiledCode (Integer -> Integer)
compiledAlwaysInlineLocal = $$(compile [||alwaysInlineLocal||])
