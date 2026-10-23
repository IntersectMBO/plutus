# keepPolicies-24: Filter a large Value

Filter a stress input with 200 policies and 200 token names per policy. Request #00c7, #0000, #0063, #0000 and absent #ffff in that order. Return the selected Value to verify its policies, token names and quantities, including duplicate and absent-ID behavior.

Policy ID list argument: `(con (list bytestring) [#00c7, #0000, #0063, #0000, #ffff])`.

Value argument (abbreviated):

```uplc
(con value [
  (#0000, [(#0000, 1), (#0001, 1), ..., (#00c7, 1)]),
  (#0001, [(#0000, 1), (#0001, 1), ..., (#00c7, 1)]),
  ...,
  (#00c7, [(#0000, 1), (#0001, 1), ..., (#00c7, 1)])
])
```

200 policies, `#0000` through `#00c7` inclusive. Each policy contains all 200 token names `#0000` through `#00c7` with quantity 1, for 40000 assets in total.

`...` abbreviates the entries described above. The full constants are in [keepPolicies-24.uplc](keepPolicies-24.uplc).

Expected result: policies #0000, #0063 and #00c7, each with token names #0000 through #00c7 and quantity 1 (600 assets in total).
