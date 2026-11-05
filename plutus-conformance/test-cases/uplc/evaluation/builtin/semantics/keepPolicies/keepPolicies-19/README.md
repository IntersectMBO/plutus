# keepPolicies-19: 257 distinct IDs

257 distinct matching IDs exceed the input-list limit, even though every policy is present.

Policy ID list argument (abbreviated): `(con (list bytestring) [#0000, #0001, ..., #0100])`.

257 consecutive two-byte IDs, `#0000` through `#0100` inclusive.

Value argument (abbreviated): `(con value [ (#0000, [(#, 1)]), (#0001, [(#, 1)]), ..., (#0100, [(#, 1)]) ])`.

257 policies, `#0000` through `#0100` inclusive, each containing the empty token name with quantity 1.

`...` abbreviates the entries described above. The full constants are in [keepPolicies-19.uplc](keepPolicies-19.uplc).

Expected result: `evaluation failure`.
