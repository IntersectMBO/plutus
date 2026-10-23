# keepPolicies-12: Maximum-length policy

A 32-byte policy ID is valid; preserve the signed quantity and 32-byte token name when retained.

Policy ID list argument:

```uplc
(con (list bytestring) [#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff])
```

Value argument:

```uplc
(con value [(#00, [(#, -170141183460469231731687303715884105728)]),
      (#0000, [(#01, 170141183460469231731687303715884105727)]),
      (#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, [(#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, -1)])])
```

Expected result:

```uplc
(con value [(#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, [(#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, -1)])])
```
