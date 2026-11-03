# keepPolicies-05: Absent policy

An absent policy has no effect on selection.

Policy ID list argument: `(con (list bytestring) [#dd])`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

Expected result:

```uplc
(con value [])
```
