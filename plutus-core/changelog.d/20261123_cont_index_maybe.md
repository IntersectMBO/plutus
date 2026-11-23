### Changed

`Data.RandomAccessList.SkewBinary.contIndexOne` now takes a single continuation
instead of separate failure and success arguments. Its type changed from:

```haskell
contIndexOne :: forall a b. b -> (a -> b) -> RAList a -> Word64 -> b
```

to:

```haskell
contIndexOne :: forall a b. (Maybe a -> b) -> RAList a -> Word64 -> b
```

The continuation receives `Nothing` for an out-of-bounds index or `Just x` for a
successful lookup. Callers should construct their failure result in the `Nothing`
branch to avoid wasting allocations on successful lookups.
