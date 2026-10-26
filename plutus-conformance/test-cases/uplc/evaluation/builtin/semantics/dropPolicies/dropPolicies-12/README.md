# dropPolicies-12: Maximum-length policy

Remove the policy with a 32-byte ID, including its 32-byte token name and negative quantity; retain the two other policies.

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
(con value [(#00, [(#, -170141183460469231731687303715884105728)]),
      (#0000, [(#01, 170141183460469231731687303715884105727)])])
```
