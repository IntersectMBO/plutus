# multiIndexArray-14: Index beyond the machine integer range fails without wrapping

Array argument: `(con (array integer) [10, 20, 30, 40, 50])`.

Index argument: `(con (list integer) [18446744073709551616])`.

Expected result: `evaluation failure`. The index must be checked before
conversion to a machine integer, so it cannot wrap to zero.
