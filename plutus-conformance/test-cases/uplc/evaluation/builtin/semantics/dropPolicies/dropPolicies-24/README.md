# dropPolicies-24: Filter a large Value

Filter a stress input with 200 policies and 200 token names per policy. Request #00c7, #0000, #0063, #0000 and absent #ffff in that order. Observe policies of the result to distinguish the remaining set from the selected set and catch an incorrect policy selection.

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

`...` abbreviates the entries described above. The full constants are in [dropPolicies-24.uplc](dropPolicies-24.uplc).

Expected result: the 197 policy IDs #0001 through #00c6, excluding #0063, in ascending byte order.
