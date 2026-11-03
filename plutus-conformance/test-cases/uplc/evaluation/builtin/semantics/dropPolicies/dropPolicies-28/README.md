# dropPolicies-28: Retain negative quantities in the complement

Remove #aa while keeping lovelace, #bb and #cc unchanged. The negative quantity under #bb is valid and must not make dropPolicies fail.

Policy ID list argument: `(con (list bytestring) [#aa])`.

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
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```
