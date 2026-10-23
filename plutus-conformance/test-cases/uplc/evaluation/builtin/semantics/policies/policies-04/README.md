# policies-04: Multiple assets per policy

Return each policy once, including lovelace, in ascending order; quantities may be negative.

Expected result:

```uplc
(con (list bytestring) [#, #aa, #bb, #cc])
```
