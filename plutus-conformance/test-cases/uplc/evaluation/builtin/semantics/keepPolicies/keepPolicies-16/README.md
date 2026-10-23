# keepPolicies-16: 256 repeated matching IDs

A list of 256 copies of #aa is accepted and affects #aa exactly once.

Policy ID list argument (abbreviated): `(con (list bytestring) [#aa, #aa, ..., #aa])`.

256 entries: 256 copies of `#aa`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

`...` abbreviates the entries described above. The full constants are in [keepPolicies-16.uplc](keepPolicies-16.uplc).

Expected result:

```uplc
(con value [(#aa, [(#01, 5), (#02, -7)])])
```
