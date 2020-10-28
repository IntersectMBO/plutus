#### Scripts for `vesting` validations

| Validation number | Validator | Datum | Redeemer | Context | Comments |
|:------------------|:----------|:------|:---------|:--------| :--------|
| 1                 | 1         | 1     | 1        | 1       |          |
| 2                 | 2         | 1     | 1        | 2       |          |
| 3                 | 3         | 1     | 1        | 1       |          |

You can obtain an executable program by using the `plc` command to combine a
validator, datum, redeemer, and context (in that order) according to the above
table.  For example

```
  plc apply Validator02.plc Datum01.plc Redeemer01.plc Context02.plc -o Validation2.plc
```
