# dropPolicies-15: 256 matching policy IDs

Request #0000 through #00ff from a Value with 257 policies. #0100 belongs to the complement.

Expected result:

```uplc
(con value [(#0100, [(#, 1)])])
```
