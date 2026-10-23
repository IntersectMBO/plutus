# keepPolicies-27: Negative quantities remain after filtering

Use the same Value and valueContains operand as the preceding case, changing only the policy list so a negative amount remains. valueContains must fail because its first argument still contains a negative quantity.

Policy ID list argument: `(con (list bytestring) [#bb])`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

Second valueContains argument: `(con value [(#cc, [(#01, 1)])])`.

Expected result: `evaluation failure`.
