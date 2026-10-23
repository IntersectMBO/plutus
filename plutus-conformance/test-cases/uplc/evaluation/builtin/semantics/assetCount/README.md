# assetCount conformance cases

These fixtures cover [CIP-0168](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0168) and the current repository implementation.

```haskell
assetCount :: Value -> Integer
```

Count distinct (policy ID, token name) pairs, including lovelace, regardless of the sign or magnitude of nonzero quantities.

A stress case uses a Value with 200 policies and 200 token names per policy (40000 assets). The builtin requires no force.
