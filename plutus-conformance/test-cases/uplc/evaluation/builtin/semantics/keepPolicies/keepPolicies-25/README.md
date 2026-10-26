# keepPolicies-25: Remove policies containing negative quantities

Keep lovelace and #cc while removing #aa and #bb.

Policy ID list argument: `(con (list bytestring) [#, #cc])`.

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
