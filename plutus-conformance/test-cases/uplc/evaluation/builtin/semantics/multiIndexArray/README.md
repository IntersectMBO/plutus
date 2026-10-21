# multiIndexArray conformance cases

These fixtures cover [CIP-0156](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0156)
and the current repository implementation:

```haskell
multiIndexArray :: forall a. Array a -> List Integer -> List a
```

The builtin takes the array first and requires one force. Indices are zero-based;
result order and duplicates follow the index list. Any out-of-bounds index fails
the whole call. An empty index list succeeds even for an empty array. Requests
of at most 1,024 indices are accepted; 1,025 indices fail even when all are valid.
