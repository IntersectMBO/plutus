### Added

- `asData` now generates a destructor function for the data type, in addition to the
  pattern synonyms. For sum types, it is better to use the destructor function than the
  pattern synonyms to match on them.
