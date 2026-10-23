# assetCount-07: More than 256 policies

A Value with 257 policies and one token per policy has 257 assets.

Value argument (abbreviated): `(con value [ (#0000, [(#, 1)]), (#0001, [(#, 1)]), ..., (#0100, [(#, 1)]) ])`.

257 policies, `#0000` through `#0100` inclusive, each containing the empty token name with quantity 1.

`...` abbreviates the entries described above. The full constants are in [assetCount-07.uplc](assetCount-07.uplc).

Expected result:

```uplc
(con integer 257)
```
