# dropPolicies-15: 256 matching policy IDs

Request #0000 through #00ff from a Value with 257 policies. #0100 belongs to the complement.

Policy ID list argument (abbreviated): `(con (list bytestring) [#0000, #0001, ..., #00ff])`.

256 consecutive two-byte IDs, `#0000` through `#00ff` inclusive.

Value argument (abbreviated): `(con value [ (#0000, [(#, 1)]), (#0001, [(#, 1)]), ..., (#0100, [(#, 1)]) ])`.

257 policies, `#0000` through `#0100` inclusive, each containing the empty token name with quantity 1.

`...` abbreviates the entries described above. The full constants are in [dropPolicies-15.uplc](dropPolicies-15.uplc).

Expected result:

```uplc
(con value [(#0100, [(#, 1)])])
```
