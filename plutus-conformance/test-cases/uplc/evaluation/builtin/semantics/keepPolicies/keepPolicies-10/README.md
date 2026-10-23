# keepPolicies-10: Mixed known and absent policies

Absent IDs before and after a matching policy do not change the result.

Policy ID list argument: `(con (list bytestring) [#dd, #bb, #ee])`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

Expected result:

```uplc
(con value [(#bb, [(#, -2), (#ff, 9)])])
```
