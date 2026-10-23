# policies conformance cases

These fixtures cover [CIP-0168](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0168) and the current repository implementation.

```haskell
policies :: Value -> List ByteString
```

Return policy IDs once each, in ascending byte order, including the empty lovelace policy ID when present.

A stress case uses a Value with 200 policies and 200 token names per policy (40000 assets). The builtin requires no force.
