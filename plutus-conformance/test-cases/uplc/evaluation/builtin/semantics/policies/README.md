# policies conformance cases

These fixtures cover [CIP-0168](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0168).

```haskell
policies :: Value -> List ByteString
```

Return policy IDs once each, in ascending byte order, including the empty lovelace policy ID when present.

The builtin requires no force.
