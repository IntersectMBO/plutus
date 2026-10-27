# assetCount-05: Multiple policies and signed quantities

Count six distinct policy/token pairs, including lovelace and negative quantities. The same token name under different policies counts separately.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

Expected result:

```uplc
(con integer 6)
```
