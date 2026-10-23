# keepPolicies-26: No negative quantities after filtering

Filter a Value containing negative amounts under #aa and #bb so neither negative policy remains. The filtered Value must contain the positive #cc asset: valueContains succeeds after removed negatives cease to affect the result.

Policy ID list argument: `(con (list bytestring) [#, #cc])`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

Second valueContains argument: `(con value [(#cc, [(#01, 1)])])`.

Expected result:

```uplc
(con bool True)
```
