# dropPolicies-07: All policies

Request every policy, including lovelace, in reverse order.

Policy ID list argument: `(con (list bytestring) [#cc, #bb, #aa, #])`.

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
