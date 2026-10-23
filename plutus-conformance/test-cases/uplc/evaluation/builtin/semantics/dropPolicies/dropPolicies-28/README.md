# dropPolicies-28: Dual law with every policy

The full selection and empty complement reconstruct the original.

Policy ID list argument: `(con (list bytestring) [#cc, #bb, #aa, #])`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

Expected result:

```uplc
(con bool True)
```
