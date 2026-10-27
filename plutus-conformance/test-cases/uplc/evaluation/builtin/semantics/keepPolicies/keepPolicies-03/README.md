# keepPolicies-03: Empty policy list

An empty policy list returns an empty Value.

Policy ID list argument: `(con (list bytestring) [])`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

Expected result:

```uplc
(con value [])
```
