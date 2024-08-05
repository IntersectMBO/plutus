### Changed

- In #6347 made `[] :: [Integer]`, `[] :: [Bool]`, `[] :: [Data]`, and `[(Data, Data)]` compile directly to the respective empty list via the `MkNil` type class without usage of built-in functions or `defineBuiltinTerm`.
