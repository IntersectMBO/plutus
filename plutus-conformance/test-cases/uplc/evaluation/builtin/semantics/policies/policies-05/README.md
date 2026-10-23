# policies-05: Bytewise ordering and maximum keys

Order #00, #0000, #01 and the 32-byte #ff policy lexicographically. Sorting by length first would put #01 before #0000 and must fail this case. Signed quantities do not affect policy enumeration.

Expected result:

```uplc
(con (list bytestring) [#00, #0000, #01, #ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff])
```
