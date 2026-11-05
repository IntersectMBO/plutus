# multiIndexArray-26: Nested array elements retain their values, order and duplicates

Array argument: `(con (array (array integer)) [[10, 20], []])`.

Index argument: `(con (list integer) [1, 0, 1])`.

Expected result: `(con (list (array integer)) [[], [10, 20], []])`.
