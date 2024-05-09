### Changed

- Renamed `PlutusTx.Builtins.matchList` to `matchList'`. The new `matchList` takes
  an argument of type `() -> r` for the `nil` case, ensuring that the nil case
  isn't evaluated if the list is non-empty.
