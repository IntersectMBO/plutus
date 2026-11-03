# keepPolicies-04: Single matching asset

Select the sole policy in a single-asset Value.

Policy ID list argument: `(con (list bytestring) [#aa])`.

Value argument: `(con value [(#aa, [(#01, 42)])])`.

Expected result:

```uplc
(con value [(#aa, [(#01, 42)])])
```
