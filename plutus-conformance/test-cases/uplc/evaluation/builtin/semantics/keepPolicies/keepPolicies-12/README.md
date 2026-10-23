# keepPolicies-12: Maximum-length policy

A 32-byte policy ID is valid; preserve the signed quantity and 32-byte token name when retained.

Expected result:

```uplc
(con value [(#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, [(#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, -1)])])
```
