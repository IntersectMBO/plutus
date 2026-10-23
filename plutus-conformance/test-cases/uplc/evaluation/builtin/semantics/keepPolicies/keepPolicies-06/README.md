# keepPolicies-06: Subset in reverse order with duplicates

Request #cc, #aa, #aa in that order. Keep all tokens of those policies once; the output remains canonical and signed quantities are preserved.

Policy ID list argument: `(con (list bytestring) [#cc, #aa, #aa])`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

Expected result:

```uplc
(con value [(#aa, [(#01, 5), (#02, -7)]),
      (#cc, [(#01, 1)])])
```
