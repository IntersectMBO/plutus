# policies-05: Bytewise ordering and maximum keys

Policy IDs are returned in bytewise order, with #0000 before #01. Signed quantities do not affect enumeration.

Value argument:

```uplc
(con value [(#00, [(#, -170141183460469231731687303715884105728)]),
      (#0000, [(#01, 170141183460469231731687303715884105727)]),
      (#01, [(#, 1)]),
      (#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, [(#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, -1)])])
```

Expected result:

```uplc
(con (list bytestring) [#00, #0000, #01, #ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff])
```
