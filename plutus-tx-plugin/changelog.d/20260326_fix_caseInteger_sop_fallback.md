### Fixed

- Fixed a 3-5x execution cost regression for `unsafeFromBuiltinData` on multi-constructor
  types when compiling in SumsOfProducts mode (the default). The `caseInteger` fallback
  now generates `equalsInteger`/`ifThenElse` chains instead of building a linked list at
  runtime.
