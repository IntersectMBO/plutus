# dropPolicies-27: Dual law with empty policy list

The empty selection and full complement reconstruct the original.

Policy ID list argument: `(con (list bytestring) [])`.

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
