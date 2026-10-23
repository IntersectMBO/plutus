# dropPolicies-10: Mixed known and absent policies

Absent IDs before and after a matching policy do not change the result.

Expected result:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#cc, [(#01, 1)])])
```
