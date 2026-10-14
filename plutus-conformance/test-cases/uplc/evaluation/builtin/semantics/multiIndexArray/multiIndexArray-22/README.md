# multiIndexArray-22: Unit elements retain their values, order and duplicates

Array argument: `(con (array unit) [(), ()])`.

Index argument: `(con (list integer) [1, 0, 1])`.

Expected result: `(con (list unit) [(), (), ()])`. Unit values are
indistinguishable; the result checks the element type and list length.
