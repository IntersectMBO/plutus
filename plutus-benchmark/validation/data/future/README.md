## Scripts for `future` validations

| Validation number | Validator | Datum | Redeemer | Context | Comments |
|:------------------|:----------|:------|:---------|:--------| :--------|
| 1                 | 1         | 1     | 1        | 1       |          |
| 2                 | 2         | 2     | 1        | 2       |          |
| 3                 | 2         | 3     | 1        | 3       |          |
| 4                 | 3         | 4     | 2        | 4       |          |
| 5                 | 3         | 5     | 3        | 5       |          |
| 6                 | 3         | 4     | 4        | 6       |          |
| 7                 | 3         | 4     | 3        | 7       |          |

You can obtain an executable program by using the `plc` command to combine a
validator, datum, redeemer, and context (in that order) according to the above
table.  For example

```
  plc apply Validator03.plc Datum04.plc Redeemer02.plc Context04.plc -o Validation4.plc
``

