# policies-03: Lovelace only

The lovelace policy ID is the empty bytestring.

Value argument: `(con value [(#, [(#, 1000000)])])`.

Expected result:

```uplc
(con (list bytestring) [#])
```
