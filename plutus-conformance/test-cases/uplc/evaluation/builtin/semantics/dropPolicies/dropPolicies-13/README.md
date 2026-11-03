# dropPolicies-13: 255 policy IDs

255 distinct absent IDs are below the input-list limit.

Policy ID list argument (abbreviated): `(con (list bytestring) [#0000, #0001, ..., #00fe])`.

255 consecutive two-byte IDs, `#0000` through `#00fe` inclusive.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

`...` abbreviates the entries described above. The full constants are in [dropPolicies-13.uplc](dropPolicies-13.uplc).

Expected result:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```
