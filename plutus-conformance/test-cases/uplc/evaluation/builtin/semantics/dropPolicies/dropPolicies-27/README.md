# dropPolicies-27: Remove policies containing negative quantities

Remove #aa and #bb; lovelace and #cc are unchanged.

Policy ID list argument: `(con (list bytestring) [#aa, #bb])`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

Expected result:

```uplc
(con value [(#, [(#, 1000000)]),
      (#cc, [(#01, 1)])])
```
