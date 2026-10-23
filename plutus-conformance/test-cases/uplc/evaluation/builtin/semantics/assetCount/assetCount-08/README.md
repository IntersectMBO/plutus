# assetCount-08: Count a large Value

Count a stress input with 200 policies and 200 distinct token names per policy. The total is 40000 assets, matching the valueData conversion limit; assetCount itself imposes no asset-count limit.

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

`...` abbreviates the entries described above. The full constants are in [assetCount-08.uplc](assetCount-08.uplc).

Expected result:

```uplc
(con integer 40000)
```
