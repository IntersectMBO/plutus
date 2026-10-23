# dropPolicies-18: 256 overlong IDs

256 copies of a 33-byte ID are accepted and ignored.

Expected result:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```
