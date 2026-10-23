# policies-05: Bytewise ordering and maximum keys

Order #00, #0000, #01 and the 32-byte #ff policy lexicographically. Sorting by length first would put #01 before #0000 and must fail this case. Signed quantities do not affect policy enumeration.

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
