# policies-07: Policies of a large Value

Enumerate 200 policies (#0000 through #00c7), each containing 200 distinct token names. This stress input has 40000 assets.

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

`...` abbreviates the entries described above. The full constants are in [policies-07.uplc](policies-07.uplc).

Expected result: the 200 policy IDs #0000 through #00c7, in ascending byte order.
