# keepPolicies-09: Non-lovelace policies

Request all non-lovelace policies; lovelace belongs to the complement.

Policy ID list argument: `(con (list bytestring) [#aa, #bb, #cc])`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

Expected result:

```uplc
(con value [(#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```
