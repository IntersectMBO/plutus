# dropPolicies-21: 257 absent IDs

Every list entry counts, including unknown IDs.

Policy ID list argument (abbreviated): `(con (list bytestring) [#dd, #dd, ..., #dd])`.

257 entries: 257 copies of `#dd`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

`...` abbreviates the entries described above. The full constants are in [dropPolicies-21.uplc](dropPolicies-21.uplc).

Expected result: `evaluation failure`.
