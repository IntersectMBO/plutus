# keepPolicies-22: 257 overlong IDs

Every list entry counts, including 33-byte IDs that would otherwise be ignored.

Policy ID list argument (abbreviated):

```uplc
(con (list bytestring) [#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, #ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, ..., #ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff])
```

257 entries: 257 copies of `#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

`...` abbreviates the entries described above. The full constants are in [keepPolicies-22.uplc](keepPolicies-22.uplc).

Expected result: `evaluation failure`.
