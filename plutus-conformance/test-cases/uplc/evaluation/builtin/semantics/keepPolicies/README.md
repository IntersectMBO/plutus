# keepPolicies conformance cases

These fixtures cover [CIP-0168](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0168).

```haskell
keepPolicies :: List ByteString -> Value -> Value
```

Keep every asset under a requested policy ID. Input order and duplicate IDs do not affect the resulting Value.

The input policy list accepts at most 256 entries. Duplicates, absent IDs and overlong IDs all count toward this limit; 257 entries fail even for an empty Value. IDs absent from the Value, including those longer than 32 bytes, are otherwise ignored.

The builtin requires no force.
