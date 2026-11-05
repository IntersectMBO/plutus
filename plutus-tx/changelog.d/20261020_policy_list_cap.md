### Changed

- `keepPolicies` and `dropPolicies` fail on a list of more than 256 policy ids, repeated ids and ids longer than 32 bytes included, matching the builtins. Their limit of 8191 policies on the `Value` is removed.
