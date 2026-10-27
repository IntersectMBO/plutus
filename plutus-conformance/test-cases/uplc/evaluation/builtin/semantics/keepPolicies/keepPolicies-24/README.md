# keepPolicies-24: Preserve assets with duplicate policy IDs

Keep both requested policies exactly once. Lovelace and #cc belong to the complement.

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
(con value [(#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)])])
```
