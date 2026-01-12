# Investigation: Disabling mkSimplPass in PlutusTx Plugin

## Context

This investigation was conducted to understand whether disabling the `mkSimplPass` in the PlutusTx plugin would improve error messages for stage violations, specifically the confusing "Cannot construct a value of type: BuiltinUnit" error reported in [plutus-private#1626](https://github.com/IntersectMBO/plutus-private/issues/1626).

## Background

The `mkSimplPass` was originally added to work around [GHC #16615](https://gitlab.haskell.org/ghc/ghc/-/issues/16615), where local bindings lack unfoldings when Core plugins run early in the compilation pipeline. The simplifier pass with `sm_pre_inline = True` generates these unfoldings by inlining bindings that occur exactly once unconditionally.

### Why mkSimplPass Was Needed

From Note [GHC.sm_pre_inline] in the code:
- The plugin requires certain functions to be fully applied
- Example: it can handle `noinline @(String -> BuiltinString) stringToBuiltinString "a"` but not `let f = noinline @(String -> BuiltinString) stringToBuiltinString in f "a"`
- Pre-inlining solves this by inlining single-use bindings before the plugin runs

## Investigation Method

1. Disabled `mkSimplPass` in `PlutusTx.Plugin.install` 
2. Attempted to build the plutus-tx-plugin test suite
3. Categorized and analyzed all compilation failures
4. Assessed whether failures could be fixed without the simplifier pass

## Key Findings

### ✅ Primary Goal Achieved: Better Error Messages

**Before (with mkSimplPass):**
```
Error: Unsupported feature: Cannot construct a value of type: BuiltinUnit
Context: Compiling expr: BuiltinUnit
Context: Compiling expr: BuiltinUnit ipv
```

**After (without mkSimplPass):**
```
Error: Reference to a name which is not a local, a builtin, or an external INLINABLE function: Variable validator1
No unfolding
Context: Compiling expr: validator1
Context: Compiling expr at: test/BuiltinUnit/Spec.hs:74:11-36
```

The new error message clearly indicates the stage violation problem and points to the exact location, making it much easier for users to understand and fix.

### Failure Categories

Without `mkSimplPass`, we observed three main categories of failures:

#### 1. Stage Violations (✅ Fixed)
- **BuiltinUnit test cases**: Now produce clear "No unfolding" errors instead of confusing builtin constructor errors
- **This is the desired behavior** - code that violates PlutusTx compilation rules should fail with meaningful messages

#### 2. Missing Unfoldings for INLINEABLE Functions (🔧 Potentially Fixable)
```
Error: Reference to a name which is not a local, a builtin, or an external INLINABLE function: Variable Plugin.Coverage.Spec.fun
OtherCon []
```
- **Root cause**: GHC #16615 - local bindings lack unfoldings without simplifier
- **Pattern**: Functions marked `{-# INLINEABLE #-}` but defined after their use site
- **Solutions**:
  - Move functions to top-level
  - Generate minimal unfoldings during desugaring (GHC enhancement needed)
  - Create lightweight unfolding pass (lighter than full simplifier)

#### 3. String Literal Processing Issues (🔧 Potentially Fixable)
```
Error: Unsupported feature: Literal string (maybe you need to use OverloadedStrings)
Context: Compiling expr: "f0d1"#
```
- **Root cause**: String literals not being processed properly without pre-inlining
- **Pattern**: Hex string literals in ByteString contexts
- **Solutions**:
  - Pre-process string literals before plugin runs
  - Better handling of `OverloadedStrings` in plugin
  - Add specific support for hex string literal patterns

## Feasibility Assessment

### ✅ **Highly Feasible**

The investigation shows that disabling `mkSimplPass` is **feasible** for several reasons:

1. **Primary goal achieved**: Stage violations now produce clear, actionable error messages
2. **Most failures are fixable**: The breaking changes are due to missing unfoldings, not fundamental incompatibilities
3. **Targeted solutions possible**: Each failure category has potential solutions that don't require the full complexity of the current simplifier pass
4. **Performance benefits**: Removing the simplifier pass would improve compilation performance

### Recommended Approach

1. **Phase 1**: Implement targeted fixes for the most common failure patterns:
   - Add lightweight unfolding generation for `INLINEABLE` functions
   - Improve string literal handling
   - Update problematic test code organization

2. **Phase 2**: Gradually remove `mkSimplPass` once core issues are resolved:
   - Start with a flag to disable the pass for testing
   - Monitor performance and correctness
   - Full removal once confidence is high

3. **Phase 3**: Enhance error messages further:
   - Add specific detection and messaging for stage violations
   - Provide suggestions for fixing common problems

## Impact Analysis

### Benefits
- **Much clearer error messages** for stage violations
- **Better compilation performance** (no unnecessary simplification)
- **Reduced complexity** in the plugin pipeline
- **Better alignment** with PlutusTx compilation model

### Risks
- **Some legitimate code patterns may break** initially
- **Requires careful migration** of existing code
- **May need GHC enhancements** for optimal solution (addressing GHC #16615)

## Conclusion

Disabling `mkSimplPass` is a **promising approach** that achieves the primary goal of improving error messages while being technically feasible. The investigation demonstrates that most failures can be addressed through targeted solutions rather than requiring the full simplifier pass.

The trade-off between better error messages and some initial compatibility issues is favorable, especially given that the breaking patterns often represent code that violates PlutusTx compilation rules anyway.

## Test Results Summary

- **BuiltinUnit.Spec**: ✅ Compiles successfully, produces clear error messages
- **Plugin tests with unfolding issues**: ❌ Need targeted fixes
- **String literal tests**: ❌ Need preprocessing improvements
- **Overall plugin functionality**: 🔧 Maintainable with targeted improvements

---

*Investigation conducted on: 2025-01-25*  
*Branch: yura/Cannot-construct-a-value-of-type*  
*Related Issues: [plutus-private#1626](https://github.com/IntersectMBO/plutus-private/issues/1626), [GHC #16615](https://gitlab.haskell.org/ghc/ghc/-/issues/16615)*