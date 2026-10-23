# dropPolicies-20: 257 repeated matching IDs

Every list entry counts, including duplicate matching IDs.

Policy ID list argument (abbreviated): `(con (list bytestring) [#aa, #aa, ..., #aa])`.

257 entries: 257 copies of `#aa`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

`...` abbreviates the entries described above. The full constants are in [dropPolicies-20.uplc](dropPolicies-20.uplc).

Expected result: `evaluation failure`.
