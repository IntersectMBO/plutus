# dropPolicies-13: 255 policy IDs

255 distinct absent IDs are below the input-list limit.

Expected result:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```
