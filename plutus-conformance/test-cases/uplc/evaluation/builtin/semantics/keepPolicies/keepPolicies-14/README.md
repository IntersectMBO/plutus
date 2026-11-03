# keepPolicies-14: 256 policy IDs

256 distinct absent IDs are accepted at the inclusive input-list limit.

Policy ID list argument (abbreviated): `(con (list bytestring) [#0000, #0001, ..., #00ff])`.

256 consecutive two-byte IDs, `#0000` through `#00ff` inclusive.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

`...` abbreviates the entries described above. The full constants are in [keepPolicies-14.uplc](keepPolicies-14.uplc).

Expected result:

```uplc
(con value [])
```
