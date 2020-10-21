#### Scripts for `crowdfunding` validations

| Validation number | Validator | Datum | Redeemer | Context | Comments |
|:------------------|:----------|:------|:---------|:--------| :--------|
| 1                 | 1         | 1     | 1        | 1       |          |
| 2                 | 1         | 2     | 1        | 2       |          |
| 3                 | 1         | 3     | 1        | 3       |          |
| 4                 | 1         | 3     | 2        | 4       |          |
| 5                 | 1         | 1     | 2        | 5       |          |

You can obtain an executable program by using the `plc` command to combine a
validator, datum, redeemer, and context (in that order) according to the above
table.  For example

```
  plc apply Validator01.plc Datum03.plc Redeemer02.plc Context04.plc -o Validation3.plc
``

