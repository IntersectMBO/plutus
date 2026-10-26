# assetCount-04: Several token names under one policy

Three token names under one policy count as three assets.

Value argument: `(con value [(#aa, [(#, 1), (#00, 2), (#01, 3)])])`.

Expected result:

```uplc
(con integer 3)
```
