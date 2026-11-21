---
sidebar_position: 2
---

# Builtin Values

:::danger Upcoming Feature
**These functions become available at a protocol version.** The functions from [CIP-0153](https://cips.cardano.org/cip/CIP-0153) are available to Plutus V1, V2 and V3 scripts from protocol version 11. The functions from [CIP-0168](https://cips.cardano.org/cip/CIP-0168) (`policies`, `assetCount`, `keepPolicies` and `dropPolicies`) are available to all Plutus versions from protocol version 12, which also introduces Plutus V4 with all of them. The ledger rejects a script that uses a function before its protocol version.
:::

`BuiltinValue` is a Plutus Core type for multi-asset values: a map from currency symbol to a map from token name to quantity. The script context carries values as `Data`, and checking a token in that encoding means walking it. Builtin operations on a `BuiltinValue` look up or insert a token in logarithmic time, and keep, drop or count the policies and assets of a value in a single call.

**Conversion cost:** a `BuiltinValue` is decoded from `Data` with `unsafeDataAsValue`, which validates the whole encoding, so its cost grows with the size of the value. Decode a value once and reuse the result.

Functions for working with `BuiltinValue` are available in the `PlutusTx.Builtins` module:

```haskell
import PlutusTx.Builtins
  ( BuiltinValue
  , unsafeDataAsValue
  , mkValue
  , lookupCoin
  , insertCoin
  , unionValue
  , scaleValue
  , valueContains
  , policies
  , assetCount
  , keepPolicies
  , dropPolicies
  )
```

The [Haddock documentation](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Builtins.html) of these functions states what each returns and when it fails, and the [Plutus Core specification](https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf) defines them precisely.

<details>
  <summary>Example: an output that keeps a protocol's tokens</summary>
  <LiteralInclude file="Example/Builtin/Value/Main.hs" language="haskell" />

  Running it evaluates the check twice: the output that keeps the protocol's `state` token passes, and the output that loses it fails.
</details>
