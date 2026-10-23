# keepPolicies-25: Count assets after filtering

Filter a mixed-sign Value with unequal policy sizes and duplicate IDs, then count assets. Lovelace and #cc belong to the complement.

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
(con integer 4)
```
