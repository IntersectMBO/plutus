# policies-02: Single asset

One asset contributes one policy ID.

Value argument: `(con value [(#aa, [(#01, 42)])])`.

Expected result:

```uplc
(con (list bytestring) [#aa])
```
