# keepPolicies-11: Overlong policy does not match its prefix

Request a 33-byte #ff ID followed by valid #0000 from a Value containing the 32-byte #ff prefix. Ignore only the overlong ID and still process #0000. Truncating the long ID or discarding the rest of the list produces a different result.

Expected result:

```uplc
(con value [(#0000, [(#01, 170141183460469231731687303715884105727)])])
```
