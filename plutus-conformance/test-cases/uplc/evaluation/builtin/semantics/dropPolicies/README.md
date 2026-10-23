# dropPolicies conformance cases

These fixtures cover [CIP-0168](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0168) and the current repository implementation.

```haskell
dropPolicies :: List ByteString -> Value -> Value
```

Remove every asset under a requested policy ID. Input order and duplicate IDs do not affect the resulting Value. Cases 26-30 check the keep/drop partition law through unionValue and valueData.

The input policy list accepts at most 256 entries. Duplicates, absent IDs and overlong IDs all count toward this limit; 257 entries fail even for an empty Value. IDs absent from the Value, including those longer than 32 bytes, are otherwise ignored. The CIP does not yet document this list limit.

A stress case uses a Value with 200 policies and 200 token names per policy (40000 assets). The builtin requires no force.
