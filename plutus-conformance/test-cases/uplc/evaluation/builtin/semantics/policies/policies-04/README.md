# policies-04: Multiple assets per policy

Return each policy once, including lovelace, in ascending order; quantities may be negative.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

Expected result:

```uplc
(con (list bytestring) [#, #aa, #bb, #cc])
```
