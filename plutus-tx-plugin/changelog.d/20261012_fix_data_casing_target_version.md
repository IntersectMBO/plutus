## Fixed

- Fix sum-type decoding when targeting Plutus Core versions below 1.2.0 by avoiding
  unsupported `case` expressions on `Data`.
