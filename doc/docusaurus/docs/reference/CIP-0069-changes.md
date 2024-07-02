---
sidebar_position: 26
---

# Understanding CIP-0069 changes

## Overview

Cardano Improvement Proposal 69 [(CIP-0069)](https://cips.cardano.org/cip/CIP-0069) introduces significant changes to how Plutus scripts are written and executed. 
It streamlines the development and functionality of Plutus scripts by unifying the arguments that are provided to different types of scripts. 
Specifically, it removes the datum argument, which has been a source of complexity and limitations in decentralized application (DApp) development on the Cardano blockchain.
These changes also reduce the chances of attacks succeeding. 

We will review these changes and take a look at how to implement them.

## 1. Unified signature for all Plutus scripts

### What changed

Previously, different types of scripts (like spending or minting) had different structures, making it challenging to create multi-purpose scripts. 
CIP-0069 introduces a unified signature for all Plutus scripts, regardless of their purpose.
This unification simplifies the Plutus codebase and allows for more flexible script design.

### Implementation of new signature
To implement this change, it is necessary to update all scripts to use this new signature:
```haskell
ScriptArgs -> ScriptContext -> ()
```

### Example

Here's an example of a unified script: 

```haskell
{-# INLINABLE unifiedScript #-}
unifiedScript :: ScriptArgs -> ScriptContext -> ()
unifiedScript args ctx = 
  case args of
    RedeemerOnly r -> handleRedeemer r ctx
    RedeemerAndDatum r d -> handleBoth r d ctx
  where
    handleRedeemer r ctx = ...
    handleBoth r d ctx = ...
```

This code shows how a script now handles different types of inputs (`RedeemerOnly` or `RedeemerAndDatum`) within a single function.

### Key points

- The `ScriptArgs` type allows for handling both Redeemer-only and Redeemer-with-Datum cases.
- `ScriptContext` now contains all the contextual information, including what was previously passed as separate arguments.
- Scripts must return `()` (unit) to indicate successful validation.

## 2. Multi-purpose scripts

### What changed

Scripts can now serve multiple purposes, like spending and minting, within a single implementation.
This allows Plutus script developers to create more cohesive and efficient smart contract systems, reducing redundancy and potential inconsistencies between related scripts.

### Implementing with pattern matching

Use pattern matching on `ScriptContext` to determine and handle different script purposes.

### Example

```haskell
{-# INLINABLE multiPurposeScript #-}
multiPurposeScript :: ScriptArgs -> ScriptContext -> ()
multiPurposeScript args (ScriptContext _ purpose) =
  case purpose of
    Spending _ -> handleSpending args
    Minting _ -> handleMinting args
    Rewarding _ -> handleRewarding args
    Certifying _ -> handleCertifying args
    _ -> traceError "Unsupported script purpose"
  where
    handleSpending args = ...
    handleMinting args = ...
    handleRewarding args = ...
    handleCertifying args = ...
```

This code demonstrates how a single script can now handle multiple kinds of operations.

### Key points

- A single script can now handle multiple use cases (spending, minting, rewarding, certifying).
- We use pattern matching to direct the script's behavior based on its purpose.
- It is recommended to always include error handling for unexpected script purposes.

## 3. Optimization and security implications

### What changed

CIP-0069 resolves issues with cyclic dependencies between scripts and simplifies script interactions.
This change allows for more straightforward and secure protocol designs, reducing the attack surface and making audits easier.

### Benefits

Instead of having multiple specialized scripts that need to coordinate with each other, we now have flexible scripts that can adapt to different tasks, reducing complexity and potential points of failure.

When designing new features or refactoring existing ones, consider how you can use a single script for multiple related purposes. 
This often leads to more coherent and secure designs.

- Resolves interdependencies between scripts
- Enables more versatile scripts
- Simplifies interactions between different parts of a smart contract

### Best practices

- Design systems that utilize the multi-purpose capability of scripts for related functionalities
- Move more logic on-chain where possible; reduce reliance on complex off-chain logic 
- Leverage the unified and simplified structure for easier and more comprehensive security checks

## 4. Implementation

For reference, here's a checklist for updating existing scripts:

- [ ]  Update script signatures to the new unified format
- [ ]  Modify script context parsing to work with the new structure
- [ ]  Adjust NFT and token handling logic for multi-purpose scenarios
- [ ]  Ensure all scripts explicitly return `()` for successful validation
- [ ]  Implement proper error handling for different script purposes

### Conceptual general example of updating a spending script

#### Before

```haskell
{-# INLINABLE oldSpendingScript #-}
oldSpendingScript :: Datum -> Redeemer -> ScriptContext -> Bool
oldSpendingScript datum redeemer ctx = ...
```

#### After

```haskell
{-# INLINABLE newSpendingScript #-}
newSpendingScript :: ScriptArgs -> ScriptContext -> ()
newSpendingScript args ctx =
  case (scriptContextPurpose ctx, args) of
    (Spending _, RedeemerAndDatum redeemer datum) -> 
      if oldSpendingLogic datum redeemer ctx
        then ()
        else traceError "Spending validation failed"
    _ -> traceError "Invalid script usage"
  where
    oldSpendingLogic datum redeemer ctx = ...  -- Your existing logic here
```

### Key points

- The INLINABLE pragma is crucial for Plutus scripts; always include it.
- We now handle the datum and redeemer through the `ScriptArgs` type.
- Error handling is more explicit in the new format.

### Testing with `always succeeding` script

Developers can use a simple "always succeeding" script for testing basic functionality:

```haskell
alwaysSucceedingScript :: ScriptArgs -> ScriptContext -> ()
alwaysSucceedingScript _ _ = ()
```

:::tip
General performance consideration: As scripts may now combine multiple purposes due to CIP-69 changes, be mindful of potential increases in computational complexity. It's important to ensure updated scripts still operate within the Plutus script execution costs.
:::

## Conclusion

CIP-0069 represents a significant evolution in how Cardano smart contracts are written and executed. 
For developers, it requires substantial updates to existing scripts but offers more flexibility and simplicity in design. 
For the Cardano ecosystem as a whole, it promises more efficient, versatile, and potentially more secure smart contracts.

Remember: Thorough testing on a test network is crucial before deploying any updated scripts to the main Cardano network.
