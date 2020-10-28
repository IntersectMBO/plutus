## Scripts for `multisigStateMachine` validations

| Validation number | Validator | Datum | Redeemer | Context | Comments |
|:------------------|:----------|:------|:---------|:--------| :--------|
| 1                 | 1         | 1     | 1        | 1       |          |
| 2                 | 1         | 2     | 2        | 2       |          |
| 3                 | 1         | 3     | 3        | 3       |          |
| 4                 | 1         | 4     | 4        | 4       |          |
| 5                 | 1         | 5     | 5        | 5       |          |
| 6                 | 1         | 1     | 1        | 6       |          |
| 7                 | 1         | 2     | 2        | 7       |          |
| 8                 | 1         | 3     | 3        | 8       |          |
| 9                 | 1         | 4     | 4        | 9       |          |
| 10                | 1         | 5     | 5        | 10      |          |

You can obtain an executable program by using the `plc` command to combine a
validator, datum, redeemer, and context (in that order) according to the above
table.  For example

```
  plc apply Validator01.plc Datum02.plc Redeemer02.plc Context07.plc -o Validation7.plc
```
