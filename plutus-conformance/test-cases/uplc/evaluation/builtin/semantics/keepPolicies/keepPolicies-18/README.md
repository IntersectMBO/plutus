# keepPolicies-18: 256 overlong IDs

256 copies of a 33-byte ID are accepted and ignored.

Policy ID list argument (abbreviated):

```uplc
(con (list bytestring) [#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, #ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, ..., #ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff])
```

256 entries: 256 copies of `#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

`...` abbreviates the entries described above. The full constants are in [keepPolicies-18.uplc](keepPolicies-18.uplc).

Expected result:

```uplc
(con value [])
```
