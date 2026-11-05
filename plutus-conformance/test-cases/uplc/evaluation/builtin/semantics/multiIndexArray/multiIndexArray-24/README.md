# multiIndexArray-24: List elements retain their values, order and duplicates

Array argument: `(con (array (list integer)) [[10, 20], []])`.

Index argument: `(con (list integer) [1, 0, 1])`.

Expected result: `(con (list (list integer)) [[], [10, 20], []])`.
