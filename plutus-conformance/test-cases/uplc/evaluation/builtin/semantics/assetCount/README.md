# assetCount conformance cases

These fixtures cover [CIP-0168](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0168).

```haskell
assetCount :: Value -> Integer
```

Count distinct (policy ID, token name) pairs, including lovelace, regardless of the sign or magnitude of nonzero quantities.

The builtin requires no force.
