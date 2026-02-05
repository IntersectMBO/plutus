{-# LANGUAGE DataKinds #-}
-- Strict is required to trigger the stage violations - GHC's strictness
-- analysis converts where-bound builtin values into case expressions that
-- the plugin cannot compile. Do not remove this extension.
{-# LANGUAGE Strict #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}

{-| Tests for stage violation error messages with builtin types.

These tests verify that the plugin produces helpful error messages when
where-bindings inside compile quotations trigger stage violations.

GHC simplification converts where-bound builtin values into pattern
matches on their constructors, which the plugin cannot compile.
The improved error messages guide users to move bindings to top-level. -}
module StageViolation.Spec where

import PlutusTx.Prelude

import PlutusCore.Test (goldenUPlc)
import PlutusTx (CompiledCode, compile)
import PlutusTx.Builtins.Internal (BuiltinInteger, mkNilData, unitval)
import PlutusTx.Test ()
import Test.Tasty.Extras

tests :: TestNested
tests =
  testNested "StageViolation"
    . pure
    $ testNestedGhc
      [ goldenUPlc "builtinUnit_unitval" builtinUnitUnitval
      , goldenUPlc "builtinUnit_local" builtinUnitLocal
      , goldenUPlc "builtinUnit_toOpaque" builtinUnitToOpaque
      , goldenUPlc "builtinData" builtinDataWhereBinding
      , goldenUPlc "builtinByteString" builtinByteStringWhereBinding
      , goldenUPlc "builtinString" builtinStringWhereBinding
      , goldenUPlc "builtinList" builtinListWhereBinding
      , -- BuiltinInteger is a type alias (not opaque), so compiles successfully
        goldenUPlc "builtinInteger_notOpaque" builtinIntegerWhereBinding
      ]

-- BuiltinUnit

-- | Stage violation from direct @unitval@ reference in a where-binding.
builtinUnitUnitval :: CompiledCode BuiltinUnit
builtinUnitUnitval = $$(compile [||validator||])
  where
    validator :: BuiltinUnit
    validator = unitval
    {-# INLINEABLE validator #-}

-- | Stage violation from indirect reference through a local helper.
builtinUnitLocal :: CompiledCode BuiltinUnit
builtinUnitLocal = $$(compile [||validator||])
  where
    validator :: BuiltinUnit
    validator = localHelper
    {-# INLINEABLE validator #-}

    localHelper :: BuiltinUnit
    localHelper = unitval
    {-# INLINEABLE localHelper #-}

-- | Stage violation from @toOpaque ()@ in a where-binding.
builtinUnitToOpaque :: CompiledCode BuiltinUnit
builtinUnitToOpaque = $$(compile [||validator||])
  where
    validator :: BuiltinUnit
    validator = toOpaque ()
    {-# INLINEABLE validator #-}

-- BuiltinData

-- | Stage violation with BuiltinData in a where-binding.
builtinDataWhereBinding :: CompiledCode BuiltinData
builtinDataWhereBinding = $$(compile [||validator||])
  where
    validator :: BuiltinData
    validator = toBuiltinData (0 :: Integer)
    {-# INLINEABLE validator #-}

-- BuiltinByteString

-- | Stage violation with BuiltinByteString in a where-binding.
builtinByteStringWhereBinding :: CompiledCode BuiltinByteString
builtinByteStringWhereBinding = $$(compile [||validator||])
  where
    validator :: BuiltinByteString
    validator = emptyByteString
    {-# INLINEABLE validator #-}

-- BuiltinString

-- | Stage violation with BuiltinString in a where-binding.
builtinStringWhereBinding :: CompiledCode BuiltinString
builtinStringWhereBinding = $$(compile [||validator||])
  where
    validator :: BuiltinString
    validator = emptyString
    {-# INLINEABLE validator #-}

-- BuiltinList

-- | Stage violation with BuiltinList in a where-binding.
builtinListWhereBinding :: CompiledCode (BuiltinList BuiltinData)
builtinListWhereBinding = $$(compile [||validator||])
  where
    validator :: BuiltinList BuiltinData
    validator = mkNilData unitval
    {-# INLINEABLE validator #-}

-- BuiltinInteger (type alias, not opaque)

{-| BuiltinInteger compiles successfully because it's a type alias, not an
opaque wrapper type. This test verifies that BuiltinInteger in a where-binding
does NOT trigger the stage violation error. -}
builtinIntegerWhereBinding :: CompiledCode BuiltinInteger
builtinIntegerWhereBinding = $$(compile [||validator||])
  where
    validator :: BuiltinInteger
    validator = 42
    {-# INLINEABLE validator #-}
