# dropPolicies-30: Dual law at 256 IDs

The partition law holds at the inclusive list limit, with duplicates and absent IDs.

Policy ID list argument (abbreviated): `(con (list bytestring) [#bb, #, #dd, #dd, ..., #dd])`.

256 entries: `#bb`, then `#`, then 254 copies of `#dd`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

`...` abbreviates the entries described above. The full constants are in [dropPolicies-30.uplc](dropPolicies-30.uplc).

Expected result:

```uplc
(con bool True)
```
