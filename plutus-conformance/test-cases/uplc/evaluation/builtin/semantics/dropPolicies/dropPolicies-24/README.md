# dropPolicies-24: Preserve the complement with duplicate policy IDs

Remove #aa and #bb, leaving lovelace and #cc unchanged. A repeated ID has no further effect.

Policy ID list argument: `(con (list bytestring) [#aa, #bb, #aa])`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

Expected result:

```uplc
(con value [(#, [(#, 1000000)]),
      (#cc, [(#01, 1)])])
```
