# dropPolicies conformance cases

These fixtures cover [CIP-0168](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0168).

```haskell
dropPolicies :: List ByteString -> Value -> Value
```

Remove every asset under a requested policy ID. Input order and duplicate IDs do not affect the resulting Value. Cases 25-26 check the keep/drop partition law through unionValue and valueData.

The input policy list accepts at most 256 entries. Duplicates, absent IDs and overlong IDs all count toward this limit; 257 entries fail even for an empty Value. IDs absent from the Value, including those longer than 32 bytes, are otherwise ignored.

The builtin requires no force.
