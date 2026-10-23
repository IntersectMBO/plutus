# dropPolicies-29: Dual law with duplicates and absent IDs

An unordered selection with duplicates, lovelace, an absent ID and an overlong ID partitions a Value with positive and negative quantities.

Policy ID list argument:

```uplc
(con (list bytestring) [#bb, #, #dd, #bb, #ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff])
```

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

Expected result:

```uplc
(con bool True)
```
