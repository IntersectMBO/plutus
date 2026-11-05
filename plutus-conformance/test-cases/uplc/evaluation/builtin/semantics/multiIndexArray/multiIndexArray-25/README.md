# multiIndexArray-25: Pair elements retain their values, order and duplicates

Array argument: `(con (array (pair integer bool)) [(10, False), (20, True)])`.

Index argument: `(con (list integer) [1, 0, 1])`.

Expected result: `(con (list (pair integer bool)) [(20, True), (10, False), (20,
True)])`.
