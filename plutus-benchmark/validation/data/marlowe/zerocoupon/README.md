## Scripts for Marlowe `Zero Coupon` validations

| Validation number | Validator | Datum | Redeemer | Context | Comments |
|:------------------|:----------|:------|:---------|:--------| :--------|
| 1                 | 1         | 1     | 1        | 1       |          |
| 2                 | 1         | 2     | 2        | 2       |          |

You can obtain an executable program by using the `plc` command to combine a
validator, datum, redeemer, and context (in that order) according to the above
table.  For example

```
  plc apply Validator01.plc Datum02.plc Redeemer02.plc Context02.plc -o Validation2.plc
```
