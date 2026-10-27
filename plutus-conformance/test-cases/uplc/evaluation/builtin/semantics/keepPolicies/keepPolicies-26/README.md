# keepPolicies-26: Retain a policy containing negative quantities

Keep #bb with both token names and their original signed quantities. Negative quantities are valid and must not make keepPolicies fail.

Policy ID list argument: `(con (list bytestring) [#bb])`.

Value argument:

```uplc
(con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
```

Expected result:

```uplc
(con value [(#bb, [(#, -2), (#ff, 9)])])
```
