# assetCount-02: Lovelace and native assets

Lovelace and two token names under one native policy count as three assets.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
            (#aa, [(#01, 42), (#02, 7)])])
```

Expected result:

```uplc
(con integer 3)
```
