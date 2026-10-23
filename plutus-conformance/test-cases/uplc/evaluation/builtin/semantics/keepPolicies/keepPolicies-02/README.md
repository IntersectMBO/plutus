# keepPolicies-02: Empty Value with requested policy

A requested policy is absent from an empty Value.

Policy ID list argument: `(con (list bytestring) [#aa])`.

Value argument: `(con value [])`.

Expected result:

```uplc
(con value [])
```
