# multiIndexArray-23: Data elements retain their values, order and duplicates

Array argument: `(con (array data) [Constr 1 [I 10], List [B #ff, I 20]])`.

Index argument: `(con (list integer) [1, 0, 1])`.

Expected result: `(con (list data) [List [B #ff, I 20], Constr 1 [I 10], List [B
#ff, I 20]])`.
