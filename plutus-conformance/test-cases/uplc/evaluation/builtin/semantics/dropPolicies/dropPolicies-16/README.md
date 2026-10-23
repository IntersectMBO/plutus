# dropPolicies-16: 256 repeated matching IDs

A list of 256 copies of #aa is accepted and affects #aa exactly once.

Expected result:

```uplc
(con value [(#, [(#, 1000000)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```
