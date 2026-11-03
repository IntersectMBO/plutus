# dropPolicies-04: Single matching asset

Remove the sole policy from a single-asset Value, producing an empty Value.

Policy ID list argument: `(con (list bytestring) [#aa])`.

Value argument: `(con value [(#aa, [(#01, 42)])])`.

Expected result:

```uplc
(con value [])
```
