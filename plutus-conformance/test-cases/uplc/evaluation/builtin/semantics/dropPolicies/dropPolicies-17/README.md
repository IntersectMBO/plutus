# dropPolicies-17: 256 IDs on empty Value

The inclusive limit is also accepted for an empty Value.

Policy ID list argument (abbreviated): `(con (list bytestring) [#aa, #aa, ..., #aa])`.

256 entries: 256 copies of `#aa`.

Value argument: `(con value [])`.

`...` abbreviates the entries described above. The full constants are in [dropPolicies-17.uplc](dropPolicies-17.uplc).

Expected result:

```uplc
(con value [])
```
