# keepPolicies-16: 256 repeated matching IDs

A list of 256 copies of #aa is accepted and affects #aa exactly once.

Expected result:

```uplc
(con value [(#aa, [(#01, 5), (#02, -7)])])
```
