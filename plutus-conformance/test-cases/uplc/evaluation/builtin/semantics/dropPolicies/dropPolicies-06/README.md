# dropPolicies-06: Subset in reverse order with duplicates

Request #cc, #aa, #aa in that order. Remove all tokens of those policies once; the output remains canonical and signed quantities are preserved.

Expected result:

```uplc
(con value [(#, [(#, 1000000)]),
      (#bb, [(#, -2), (#ff, 9)])])
```
