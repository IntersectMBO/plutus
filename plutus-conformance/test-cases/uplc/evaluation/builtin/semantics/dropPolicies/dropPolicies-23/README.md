# dropPolicies-23: 257 IDs on empty Value

The limit must be enforced even when the Value is empty.

Policy ID list argument (abbreviated): `(con (list bytestring) [#aa, #aa, ..., #aa])`.

257 entries: 257 copies of `#aa`.

Value argument: `(con value [])`.

`...` abbreviates the entries described above. The full constants are in [dropPolicies-23.uplc](dropPolicies-23.uplc).

Expected result: `evaluation failure`.
